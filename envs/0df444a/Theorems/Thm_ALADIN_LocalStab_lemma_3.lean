-- Prove2me | Theorems.Thm_ALADIN_LocalStab_lemma_3
-- name    : ALADIN.LocalStab.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:20.244817+00:00
-- url     : https://prove2.me/theorems/b97d81b0-ec0d-4c47-abe7-e7495ed1d2fc
-- title:
--   Lemma 3 — near a regular KKT point the decoupled problems (3.2) have locally unique minimizers with $\|y-x^*\|\le\chi_1\|x-x^*\|+\chi_2\|\lambda-\lambda^*\|$
-- statement:
--   Consider problem (1.1),
--   $$
--   \min_x\ \sum_{i=1}^N f_i(x_i)\quad\text{s.t.}\quad \sum_{i=1}^N A_ix_i=b,\qquad h_i(x_i)\le 0,
--   $$
--   with $f_i$ and $h_i$ twice continuously differentiable. Let $x^*$ be a local minimizer of (1.1) such that $(x^*,\lambda^*,\kappa)$ is a regular KKT point (LICQ, strict complementarity, SOSC). Let $\Sigma_i$ be symmetric positive semidefinite and let $\rho>0$ be such that
--   $$
--   \forall i\in\{1,\dots,N\}:\qquad \nabla^2_x\big[f_i(x^*_i)+\kappa_i^\top h_i(x^*_i)\big] + \rho\Sigma_i \succ 0 .
--   $$
--
--   Then there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0]$ there exist constants $\chi>0$ and $\chi_1,\chi_2\ge 0$ with the following property. For every $(x,\lambda)$ with $\|x-x^*\|<\varepsilon$ and $\|\lambda-\lambda^*\|<\varepsilon$ there is $y=(y_1,\dots,y_N)$ such that
--
--   1. for every $i$, $y_i$ is a local minimizer of the decoupled problem
--   $$
--   \min_{y_i}\ f_i(y_i)+\lambda^\top A_iy_i+\frac\rho2\|y_i-x_i\|^2_{\Sigma_i}\quad\text{s.t.}\quad h_i(y_i)\le 0;
--   $$
--   2. $\|y-x^*\|<\chi\varepsilon$;
--   3. for every $i$, $y_i$ is the only local minimizer of the $i$-th decoupled problem within distance $\chi\varepsilon$ of $x^*_i$;
--   4. $\displaystyle \|y-x^*\|\le\chi_1\|x-x^*\|+\chi_2\|\lambda-\lambda^*\|$.
--
--   This is Lemma 3 of Houska, Frasch and Diehl. It says that near a regular solution, every agent's subproblem in ALADIN has a well-defined local solution that moves Lipschitz-like with the primal and dual iterates; the paper uses it to transfer local convergence rates of inexact SQP methods to the full-step variant of ALADIN.
--
--   **Formalization Note** The page's "sufficiently small open set $\mathcal N\subseteq\mathbb R^{N\cdot n}\times\mathbb R^m$ with $0\in\mathcal N$" is read as every ball of radius $\varepsilon\le\varepsilon_0$ in the sup norm of the product, i.e. $\max(\|x-x^*\|,\|\lambda-\lambda^*\|)<\varepsilon$; the constants may depend on $\varepsilon$ but not on $(x,\lambda)$. Since $y\in\mathbb R^{Nn}$ while $\mathcal N\subseteq\mathbb R^{Nn}\times\mathbb R^m$, the condition $y\in\{x^*\}\oplus\chi\mathcal N$ is read through the $x$-component: $\|y-x^*\|<\chi\varepsilon$. "Locally unique" is uniqueness among local minimizers in that same ball, block by block (equivalent to uniqueness of $(y_1,\dots,y_N)$ in the product ball). Norms are Mathlib's sup norms on `Fin N → Fin n → ℝ` and `Fin m → ℝ`; since all constants are existential, another choice of norms gives an equivalent reading. Added hypotheses, all from the paper's standing assumptions: $h_i\in C^2$ (§3, p. 1107), $\Sigma_i$ positive semidefinite (Algorithm 2, step 1, p. 1108); $\kappa$ is the inequality multiplier of the regular KKT point. A local minimizer is required to be feasible.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1117, Lemma 3

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Problem
import Definitions.Def_ALADIN_LocalStab_Decoupled

open Matrix

namespace ALADIN.LocalStab

/-- **Lemma 3** (Houska–Frasch–Diehl 2016, p. 1117). Let `fᵢ` (and, by the standing assumption of
§3, `hᵢ`) be `C²`, let `x*` be a local minimizer of (1.1) and `(x*, λ*, κ)` a regular KKT point,
let `Σᵢ ⪰ 0`, `ρ > 0` and `∇²[fᵢ + κᵢᵀhᵢ](x*ᵢ) + ρΣᵢ ≻ 0` for every block. Then for every
sufficiently small ball `𝒩` (radius `ε ∈ (0, ε₀]`, sup norm) there are constants `χ > 0`,
`χ₁, χ₂ ≥ 0` such that for every `(x, λ)` with `(x − x*, λ − λ*) ∈ 𝒩` the decoupled problems
(3.2) have local minimizers `y = (y₁, …, y_N)` with `y − x* ∈ χ𝒩` (x-component), each `yᵢ` the
only local minimizer of its problem in that ball, and `‖y − x*‖ ≤ χ₁‖x − x*‖ + χ₂‖λ − λ*‖`. -/
theorem lemma_3 {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (hSig : ∀ i, (Sig i).PosSemidef)
    (xs : Fin N → Fin n → ℝ) (lamS : Fin m → ℝ) (κ : Fin N → Fin nh → ℝ)
    (hmin : P.IsLocalMinimizer xs)
    (hreg : P.IsRegularKKTPoint xs lamS κ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ i (d : Fin n → ℝ), d ≠ 0 →
      0 < hessQuad (P.lagBlock i (κ i)) (xs i) d + ρ * (d ⬝ᵥ (Sig i *ᵥ d))) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∃ χ χ₁ χ₂ : ℝ, 0 < χ ∧ 0 ≤ χ₁ ∧ 0 ≤ χ₂ ∧
      ∀ (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ), ‖x - xs‖ < ε → ‖lam - lamS‖ < ε →
        ∃ y : Fin N → Fin n → ℝ,
          (∀ i, IsDecoupledLocalMin P ρ Sig x lam i (y i)) ∧
          ‖y - xs‖ < χ * ε ∧
          (∀ i (η : Fin n → ℝ), IsDecoupledLocalMin P ρ Sig x lam i η →
            ‖η - xs i‖ < χ * ε → η = y i) ∧
          ‖y - xs‖ ≤ χ₁ * ‖x - xs‖ + χ₂ * ‖lam - lamS‖ := by sorry

end ALADIN.LocalStab
