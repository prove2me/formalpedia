-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_actual_clipped_ceiling_grid_killed_ost_eq_nat_no_standing
-- name    : AvramDividend.Classical.p2m81_bv_actual_clipped_ceiling_grid_killed_ost_eq_nat_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T03:47:44.028897+00:00
-- url     : https://prove2.me/theorems/db3e52be-f938-43d0-a647-55e5e2c3c81c
-- title:
--   Standing-free BV clipped grid killed optional stopping equality from Esscher root
-- statement:
--   Standing-free bounded-variation clipped ceiling-grid killed optional stopping equality from a positive Esscher root, without any Standing assumption. The grid-stopped killed q-scale payoff has expectation W(x). This is the standing-free analogue of avram_ws01b_actual_clipped_ceiling_grid_killed_ost_eq_nat, needed as the OST premise for the p2m81 finite-horizon killed expectation parent.
-- source:
--   Standing-free OST premise for p2m81 parent f3582777 (BV genuine finite-horizon killed expectation no standing). Replaces Standing with BV plus positive Esscher root X.psi phi = q. Proof requires root-based BV harmonicity/martingale; further decomposition expected.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_actual_clipped_ceiling_grid_killed_ost_eq_nat_no_standing
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (a : ℝ) (T δ : ℝ≥0) (hδ : 0 < δ)
    (K : Ω → ℕ)
    (hK : ∀ η, K η = hittingBtwn
      (fun (k : ℕ) ξ => max (X.X ((k : ℝ≥0) * δ) ξ - (a-x))
        ((-x) - X.X ((k : ℝ≥0) * δ) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / δ)) η) :
    (∫ ω,
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K η : ℝ≥0) * δ) T → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * ((min ((K η : ℝ≥0) * δ) T) : ℝ))) *
          W (x + X.X (min ((K η : ℝ≥0) * δ) T) η)) ω ∂P) = W x := by sorry
