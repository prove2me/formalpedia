-- Prove2me | Theorems.Thm_BarrierTR_Global_proposition_3_2
-- name    : BarrierTR.Global.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:02.584596+00:00
-- url     : https://prove2.me/theorems/fefa1741-b001-4ac8-8103-8b5b7716dbf4
-- title:
--   Proposition 3.2, p. 19 — away from stationary points of (2.2), every step at a small enough radius is accepted
-- statement:
--   Let $(x_k,s_k)$ be a point with $s_k>0$, $B_k$ symmetric, $Z_k$ a null-space basis satisfying (2.29)–(2.30), and $\nu_{k-1}>0$. Suppose that $(x_k,s_k)$ is not a stationary point of the barrier problem (2.2), i.e. there is no $\lambda$ with $g(x_k)+s_k=0$, $\nabla f(x_k)+A(x_k)\lambda=0$ and $-\mu S_k^{-1}e+\lambda=0$. Then there exists $\Delta_k^0>0$ such that whenever Steps 1–3 of Algorithm I are carried out at a radius $\Delta_k\in(0,\Delta_k^0)$, producing $d_k$ and $\nu_k$, the slacks $s_k+(d_k)_s$ are positive and
--   $$\mathrm{ared}_k(d_k)\ \ge\ \eta\,\mathrm{pred}_k(d_k).$$
--
--   Hence Algorithm I cannot cycle forever between Steps 1 and 4: its inner loop terminates after finitely many radius reductions.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`. The positivity of $s_k+(d_k)_s$ is part of the conclusion because the paper's merit function is $+\infty$ otherwise, which would make $\mathrm{ared}_k=-\infty$. $\nu_{k-1}>0$ holds in every run, since $\nu_{-1}>0$ and the penalty never decreases.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 19, Proposition 3.2

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Proposition 3.2 (p. 19). If `s_k > 0` and `(x_k, s_k)` is not a stationary point of the barrier
problem (2.2), there is `Δ_k⁰ > 0` such that every pass through Steps 1–3 of Algorithm I at a radius
`Δ_k ∈ (0, Δ_k⁰)` yields a step `d_k` with `ared_k(d_k) ≥ η pred_k(d_k)` (in particular
`s_k + (d_k)_s > 0`, so that the merit function (2.5) is finite at the trial point). -/
theorem proposition_3_2 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (x : E n) (s : F m) (hs : ∀ i, 0 < s i)
    (B : E n →L[ℝ] E n) (hB : IsSelfAdjoint B) (Zx : E n →L[ℝ] E n) (Zs : E n →L[ℝ] F m)
    (hZ : IsNullBasis g x P.γZ Zx Zs) (νprev : ℝ) (hνprev : 0 < νprev)
    (hns : ¬ IsBarrierStationary f g P.μ x s) :
    ∃ Δ0 : ℝ, 0 < Δ0 ∧ ∀ t : Trial n m, IsTrial P f g x s B Zx Zs νprev t → t.Δ < Δ0 →
      (∀ i, 0 < s i + t.d.snd i) ∧
        P.η * pred f g P.μ t.ν x s B t.d ≤ ared f g P.μ t.ν x s t.d := by sorry

end BarrierTR.Global
