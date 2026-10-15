-- Prove2me | Theorems.Thm_FirstPriceLearning_LowerBound_eq_22
-- name    : FirstPriceLearning.LowerBound.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:45.840198+00:00
-- url     : https://prove2.me/theorems/16be41c0-c681-4bd3-a6ff-c341da4a79a9
-- title:
--   (22), p. 38 — $1-\|P_1^{\otimes T}-P_2^{\otimes T}\|_{\mathrm{TV}}\ge\tfrac12\exp(-32T\Delta^2)$
-- statement:
--   Let $\Delta\in(0,1/4)$ and $T\in\mathbb N$, let $G_1,G_2$ be the two HOB laws of the two-point construction, and let $P_i^{\otimes T}$ be the law of $T$ iid HOBs from $G_i$. Then
--
--   $$
--   1-\bigl\|P_1^{\otimes T}-P_2^{\otimes T}\bigr\|_{\mathrm{TV}}\ \ge\ \frac12\exp\bigl(-32T\Delta^2\bigr).
--   $$
--
--   Combined with the reduction (21) and the choice $\Delta=1/(4\sqrt T)$, this gives Theorem 9 with $c=1/(24e^2)$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 38, App. B, (22)

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_TVDist
import Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws

open MeasureTheory

namespace FirstPriceLearning.LowerBound

/-- arXiv:2003.09795v7, App. B, (22), p. 38: for `Δ ∈ (0, 1/4)` and every `T`,
`1 − ‖P₁^{⊗T} − P₂^{⊗T}‖_TV ≥ (1/2) exp(−32TΔ²)`. -/
theorem eq_22 (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    1 / 2 * Real.exp (-(32 * T * Δ ^ 2)) ≤
      1 - tvDist (Measure.pi fun _ : Fin T => lawG1 Δ) (Measure.pi fun _ : Fin T => lawG2 Δ) := by sorry

end FirstPriceLearning.LowerBound
