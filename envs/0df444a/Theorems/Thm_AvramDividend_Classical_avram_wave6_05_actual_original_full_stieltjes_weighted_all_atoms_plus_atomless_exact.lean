-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
-- name    : AvramDividend.Classical.avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:21:29.428982+00:00
-- url     : https://prove2.me/theorems/93720c7a-004b-4703-ae40-06eccd99de0a
-- title:
--   One exact original full Stieltjes cash identity: all right-payment atoms weighted tsum plus all atomless dividends
-- statement:
--   For any original adapted nondecreasing dividend control, any physical sample path, closed horizon and arbitrary ENNReal weight, the genuine original dividendMeasure lower integral equals exactly the sum of every right-dividend atomic weight times its original singleton mass over one countable exhaustive index set, plus the lower integral against its unchanged actual atomless component. The source rightLimit singleton identity and completeness of the countable set are supplied together. In particular f(t)=ENNReal.ofReal(exp(-qt)) gives the exact discounted original full Stieltjes dividend cash decomposition required for controlled Ito–Meyer verification, including time-zero and horizon-end right atoms, infinitely many positive jumps, absolutely continuous and singular-continuous payments. No cap, ruin, finite-jump or control smoothness hypothesis is imposed, and it is an identity rather than an inequality.
-- source:
--   Take the canonically Proved original Stieltjes atomic/atomless witness, exact arbitrary-weight lintegral split, exact atomic weighted tsum and proof that its countable support captures every nonzero original singleton. Eliminate the redundant named atomic measure by substituting the exact atom integral identity into the full original Stieltjes integral decomposition. Retain the true rightLimit payment singleton formula and the actual NullSingletonClass diffuse complement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      (∫⁻ s, f s ∂μ) =
        (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
        (∫⁻ s, f s ∂μdiffuse) := by sorry
