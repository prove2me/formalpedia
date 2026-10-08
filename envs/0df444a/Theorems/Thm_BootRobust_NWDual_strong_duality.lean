-- Prove2me | Theorems.Thm_BootRobust_NWDual_strong_duality
-- name    : BootRobust.NWDual.strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:55.333349+00:00
-- url     : https://prove2.me/theorems/084bea51-9a58-4234-a370-823cb0aba990
-- title:
--   B.8, p. 32 — for r > 0, Corollary 1's program with R = B equals inf α over (α, β, ν) with rν + νΣD·exp(((L−α)w+β)/ν − 1) ≤ β
-- statement:
--   Let $D\in\mathcal D_n$ (zeros allowed), $r>0$, $w_i>0$, and let $\ell_i=L(\bar z,\bar y_i)$ for a fixed decision $\bar z$. Let $B$ be the bootstrap distance. Then the optimal value of the program of Corollary 1 with $R=B$,
--   $$\sup_{s>0,\,P}\ \sum_iw_i\ell_iP_i\quad\text{s.t.}\quad s\,B(P/s,D)\le s\,r,\ \ \sum_iP_i=s,\ \ \sum_iw_iP_i=1,$$
--   equals the optimal value of its Lagrangian dual
--   $$\inf\Big\{\alpha\in\mathbb R:\ \exists\,\beta\in\mathbb R,\ \nu>0,\quad r\nu+\nu\sum_iD_i\exp\Big(\frac{(\ell_i-\alpha)w_i+\beta}{\nu}-1\Big)\le\beta\Big\}.$$
--
--   The condition $r>0$ is Slater's condition for the primal program, as stated in the paper. This is the strong-duality step of the proof of Lemma 2, before the multiplier $\beta$ is eliminated.
--
--   **Formalization Note** The page writes the dual function $g(\alpha,\beta,\nu)$ as the set $\{\alpha : \dots\le\beta\}$ and the dual as $\inf_{\alpha,\beta,\nu\ge0}g$; the statement reads this as the infimum of $\alpha$ over all $(\alpha,\beta,\nu)$ satisfying the constraint. $\nu>0$ replaces $\nu\ge0$ to avoid the junk value of division by zero; the infimum is unchanged. Both sides are extended reals.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.8 (proof of Lemma 2), p. 32, 'The dual optimization problem is now found as inf_{α,β,ν≥0} g(α, β, ν) … strong duality holds under Slater's condition which is satisfied whenever r > 0'

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

namespace BootRobust.NWDual

/-- B.8, p. 32 (strong duality): for `r > 0` (Slater's condition), the value of the perspective
program of Corollary 1 with `R = B` equals the infimum of `α` over the dual variables
`(α, β, ν)`, `ν > 0`, with `r ν + ν ∑ᵢ Dᵢ exp(((ℓᵢ − α) wᵢ + β)/ν − 1) ≤ β`. -/
theorem strong_duality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (r : ℝ) (hr : 0 < r)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) {Z : Type*} (L : Z → ι → ℝ) (z : Z) :
    perspValue BootRobust.Perf.bootDist D r w (L z) =
      ⨅ α ∈ {α : ℝ | ∃ β ν : ℝ, 0 < ν ∧
          r * ν + ν * ∑ i, D i * Real.exp (((L z i - α) * w i + β) / ν - 1) ≤ β},
        (α : EReal) := by sorry

end BootRobust.NWDual
