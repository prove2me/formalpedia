-- Prove2me | Theorems.Thm_ALADIN_DualDecomp_lemma_5
-- name    : ALADIN.DualDecomp.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:32.83466+00:00
-- url     : https://prove2.me/theorems/134120e8-97b6-4008-9c48-4b054caf9479
-- title:
--   Lemma 5 — with ρ = 0 the ALADIN dual iterate λ⁺ equals the dual Newton step λ⁺_DD of (A.4)
-- statement:
--   Let $(f,h,A,b)$ be an instance of problem (1.1) in which every $f_i$ and $h_i$ is twice continuously differentiable, every $f_i$ is strictly convex and every component of every $h_i$ is convex. Consider one iteration of Algorithm 2 from $(x,\lambda)$ with
--   1. penalty parameter $\rho = 0$ and positive semidefinite scaling matrices $\Sigma_i$ in step 1, and step-1 outputs $(y_i,\kappa_i)$ (so $y_i$ solves (A.2) with multiplier $\kappa_i$);
--   2. constraint Jacobian approximations $C_i\in\mathbb R^{n_h\times n}$ of full row rank and positive definite Hessian approximations $H_i$ in step 3;
--   3. any $\mu > 0$ in step 4, with $(\Delta y, s, \lambda_{\mathrm{QP}}, \nu)$ solving the KKT system of the coupled QP (3.3);
--   4. step sizes $\alpha_3 = \alpha$ with $\alpha\in(0,1]$ in step 5.
--
--   Let $M$ be given by (A.6) and $\nabla V(\lambda) = \sum_i A_i y_i - b$ by (A.3). Then $M - \frac1\mu I$ is invertible and the step-5 iterate coincides with the (inexact) dual Newton step (A.4):
--   $$\lambda^+ = \lambda + \alpha_3(\lambda_{\mathrm{QP}} - \lambda)\ =\ \lambda - \alpha\Big(M - \frac1\mu I\Big)^{-1}\nabla V(\lambda) = \lambda^+_{\mathrm{DD}},$$
--   where
--   $$M = -\sum_{i=1}^N A_i\Big[H_i^{-1} - H_i^{-1}C_i^\top\big[C_iH_i^{-1}C_i^\top\big]^{-1}C_iH_i^{-1}\Big]A_i^\top .$$
--
--   The lemma makes Remark 4.2 precise: with $\rho = 0$, ALADIN is a dual decomposition method whose dual update is a Levenberg–Marquardt-regularized dual Newton step, with $1/\mu$ as the regularization parameter.
--
--   **Formalization Note** (A.6) as printed has $[C_iH_iC_i^\top]^\dagger$; this is a typo for $[C_iH_i^{-1}C_i^\top]^\dagger$, cf. (A.5); the corrected bracket is used, and since it is invertible its pseudo-inverse is written as the inverse. The invertibility of $M - \frac1\mu I$, taken for granted on the page, is part of the conclusion because Mathlib's matrix inverse returns $0$ on singular matrices. The QP (3.3) enters through its KKT system with the sign convention of footnote 4. $\nabla V(\lambda)$ is the formula (A.3). The convexity hypotheses and $\alpha\in(0,1]$ are kept as on the page; the identity itself does not use them.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1123, Lemma 5

import Mathlib
import Definitions.Def_ALADIN_DualDecomp_Problem
import Definitions.Def_ALADIN_DualDecomp_Step

namespace ALADIN.DualDecomp

open Matrix

/-- Lemma 5 (Houska–Frasch–Diehl 2016, p. 1123), with (A.6) corrected to `[Cᵢ Hᵢ⁻¹ Cᵢᵀ]⁻¹`.
Let `fᵢ`, `hᵢ` be `C²`, `fᵢ` strictly convex and every component of `hᵢ` convex. Run one iteration of
Algorithm 2 from `(x, λ)` with `ρ = 0` and PSD scaling matrices `Σᵢ`: `(yᵢ, κᵢ)` is the step-1 output,
`Cᵢ` have full row rank, `Hᵢ` are positive definite, `μ > 0`, `(Δy, s, λ_QP, ν)` solves the KKT system
of QP (3.3), and `α₃ = α` with `α ∈ (0, 1]`. Then `M − (1/μ) I` is invertible and the step-5 iterate
`λ⁺ = λ + α₃(λ_QP − λ)` equals the dual Newton step `λ⁺_DD = λ − α (M − (1/μ) I)⁻¹ ∇V(λ)` of (A.4),
with `M` from (A.6) and `∇V(λ) = ∑ᵢ Aᵢ yᵢ − b` from (A.3). -/
theorem lemma_5 {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (hfconv : ∀ i, StrictConvexOn ℝ Set.univ (P.f i))
    (hhconv : ∀ i j, ConvexOn ℝ Set.univ (fun z => P.h i z j))
    (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ)
    (ρ : ℝ) (hρ : ρ = 0) (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (hSig : ∀ i, (Sig i).PosSemidef)
    (y : Fin N → Fin n → ℝ) (κ : Fin N → Fin nh → ℝ)
    (hstep1 : ∀ i, Step1Solution P ρ (Sig i) (x i) lam i (y i) (κ i))
    (C : Fin N → Matrix (Fin nh) (Fin n) ℝ) (hC : ∀ i, (C i).rank = nh)
    (H : Fin N → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i, (H i).PosDef)
    (μ : ℝ) (hμ : 0 < μ)
    (Δy : Fin N → Fin n → ℝ) (s : Fin m → ℝ) (lamQP : Fin m → ℝ) (ν : Fin N → Fin nh → ℝ)
    (hQP : QPKKT P lam y κ C H μ Δy s lamQP ν)
    (α α₃ : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hα₃ : α₃ = α) :
    IsUnit (Mmat P C H - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ)).det ∧
    lamPlus lam α₃ lamQP = lamDD lam α μ (Mmat P C H) (gradV P y) := by sorry

end ALADIN.DualDecomp
