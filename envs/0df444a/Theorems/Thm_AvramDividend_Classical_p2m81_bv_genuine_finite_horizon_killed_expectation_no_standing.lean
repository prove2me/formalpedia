-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_genuine_finite_horizon_killed_expectation_no_standing
-- name    : AvramDividend.Classical.p2m81_bv_genuine_finite_horizon_killed_expectation_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T00:13:36.54077+00:00
-- url     : https://prove2.me/theorems/f3582777-9357-4e66-a07d-7cb0a45dadf9
-- title:
--   Standing-free BV genuine finite-horizon killed expectation on a mesh grid
-- statement:
--   The genuine original-Levy killed finite-horizon stopped payoff Z is Bochner integrable with expectation Wq(x) under BV with a positive Esscher root X.psi phi = q, on any genuine mesh grid with the exact sampled boundary-crossing index, with no Standing assumption. This is the standing-free analogue of avram_ws01b_bv_genuine_finite_horizon_killed_expectation_unconditional; its proof replays the accepted grid optional-stopping, a.e. convergence and integral-convergence chain with root-based drift positivity and Laplace growth in place of Standing.
-- source:
--   Standing-free mesh-grid Z-balance: root-based drift positivity (BV Laplace rearrangement), root-based Laplace growth (replay of psi_eventually_gt_of_boundedVariation proof with root drift), standing-free grid integrable/a.e.-convergence/OST premises, then the already standing-free masked capped grid integral convergence 67a550ca. Child p2m81 S-balance applies this with a dyadic mesh and rewrites Z=S via the standing-free two-way split 27c65973.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_genuine_finite_horizon_killed_expectation_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
     :
    (let Z : Ω → ℝ := fun ω =>
      if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
        if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min (min
            (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
              W (x + X.X (min (min
                (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else if twoSidedExitDownTime X (-x) ω <
              twoSidedExitUpTime X (a-x) ω then 0
      else Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω);
    Integrable Z P ∧ (∫ ω, Z ω ∂P) = W x) := by sorry
