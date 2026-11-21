-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_E_original_canonical_raw_V_gap_exact_defect
-- name    : AvramDividend.Classical.avram_jump6_E_original_canonical_raw_V_gap_exact_defect
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:48:37.900875+00:00
-- url     : https://prove2.me/theorems/7e3d152f-88a8-4f28-a826-f626edcec61b
-- title:
--   Exact original canonical stopped raw-w versus caplinear-V physical payment deficit
-- statement:
--   Exact original stopped canonical-grid decomposition of raw prepayment payment-loss into a caplinear-V payment-loss plus the explicit above-cap w-versus-V defect, for the SAME spectrally negative Lévy source X, right-limit dividend strategy D, clock τ, grid indices and discount. Pure finite-grid algebra, imposing no extra growth or centring hypotheses and without silently replacing raw w by V. This fixes the missing obligation exposed by the mathematically false original raw-w finite-cap Stieltjes limit: the final signed defect must be controlled separately, while the V-grid term is covered by already Proved e0170ed2 and ce331276.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_E_original_canonical_raw_V_gap_exact_defect
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w V : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (ω : Ω) (n j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (τ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let m : ℕ := (n + 1) * (j + 1)
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) =
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (V (Y (v (i + 1))) - V (Z i))) +
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) *
        ((w (Y (v (i + 1))) - V (Y (v (i + 1)))) -
         (w (Z i) - V (Z i)))) := by sorry
