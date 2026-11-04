-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_dense_tests
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_dense_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:32:42.847379+00:00
-- url     : https://prove2.me/theorems/f5b475db-5e80-4832-8422-abe9db76d214
-- title:
--   Original separated Borel rate from analytic dense halfline tests
-- statement:
--   For an actual original spectrally negative Lévy process and a separated negative Borel mark set, the full expected jump count equals elapsed time times ν(B), provided the source-dependent rate identity has first been proved for cutoff lower-halfline tests on a dense family of real thresholds. The theorem packages exact original expected mark measure construction, finite Lévy comparison measure and dense Borel extension. The dense halfline rate tests remain a genuine external analytic hypothesis, so this is a conditional reduction and does not establish the missing zero-origin Lévy rate unconditionally.
-- source:
--   P2-C uses Proved P2-A separated ν finite helper 86086cb2, together with P2-C scaled comparator finite and original marked measure extension without pre-assumed finite source mean. It explicitly does not use Open 34dbea70 and leaves analytic dense tests as a hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_separated_rate_from_dense_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε))
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic a ∩ Iic (-ε)))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
