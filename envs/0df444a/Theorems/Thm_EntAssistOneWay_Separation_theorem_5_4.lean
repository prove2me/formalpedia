-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_5_4
-- name    : EntAssistOneWay.Separation.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:28.11732+00:00
-- url     : https://prove2.me/theorems/efbf44e3-4f59-4e6d-b34c-aa0c04edbb85
-- title:
--   Theorem 5.4 — independent-phase correlation estimate
-- statement:
--   Let $G,\zeta,D$ satisfy the standing central order-three and dimension-gap assumptions, let $r\ge1$, and set $S=\mathbb F_2^r$. For maps $w_s:G^S\to\mathbb C$ bounded in modulus by one, define $\operatorname{Corr}$ and $\operatorname{Corr}_{\rm ind}$ as on p. 27. Then
--   $$\left|\mathbb E_{g_1,g_2}\operatorname{Corr}(g_1,g_2)-\mathbb E_{g_1,g_2,\phi}\operatorname{Corr}_{\rm ind}(g_1,g_2,\phi)\right|\le\frac{2^r-1}{D}.$$
--   All arrays and all phase coordinates are sampled independently and uniformly. Each phase multiplies every coordinate of the relevant shifted product. The estimate is the scalar analytic comparison used for matrix moments.
--
--   Differences from the source:
--   - generalization: D is the least dimension of an irrep nontrivial on ζ → any integer D ≥ 1 for which all lower-dimensional representations kill ζ; reason: complete reducibility and unitarisability for finite groups give the source instance; the estimates use only this lower-dimensional vanishing
--   - encoding: uniform arrays and a phase vector in F₃^S → uniform averages on finite product and function types; reason: each coordinate and each array has the required independent uniform distribution
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 27, Theorem 5.4; pp. 31–33, proof

import Definitions.Def_EntAssistOneWay_Separation_GroupAnalysis

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 5.4, p. 27; phase rotation is applied to every coordinate. -/
theorem theorem_5_4 (G : Type) [Group G] [Fintype G] (r : ℕ) (hr : 1 ≤ r)
    (ζ : G) (D : ℕ) (hζ : CentralThree ζ) (hD : DimensionGap ζ D)
    (w : ShiftSpace r → (ShiftSpace r → G) → ℂ) (hw : ∀ s h, ‖w s h‖ ≤ 1) :
    ‖uniformAverage (fun t : ShiftAlice G r => correlation w t.1 t.2) -
      uniformAverage (fun t : ShiftAlice G r × (ShiftSpace r → ZMod 3) =>
        independentCorrelation ζ w t.1.1 t.1.2 t.2)‖ ≤
      ((2 : ℝ) ^ r - 1) / D := by sorry

end

end EntAssistOneWay.Separation
