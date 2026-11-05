-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_chronological_pair_mean_exact
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_mean_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:10:02.528586+00:00
-- url     : https://prove2.me/theorems/d938e9a5-b97c-409b-bffb-bfef53c53ef0
-- title:
--   Genuine original negative-band chronological pair count has exact second factorial mean
-- statement:
--   For the same original spectrally negative Lévy path X on Ω and its literal finite set of negative-band jump times in (0,T], the chronological ordered-pair count K is real-L1 and E[2K]=(Tν(B))², where B is exactly (-∞,-1/(n+1)]. This is the remaining nontrivial source second-factorial-moment theorem required by the accepted physical pathwise count J²=J+2K identity and P4-F centred L2/Itô–Meyer work. The result must be derived using original-source predictable compensation and justified finite-grid refinement, with no replacement Poisson model.
-- source:
--   Original P2-E source rectangle compensator 393b03a8, source weighted past factor 267e2229, physical negative-band finite jump-time theorem e5e6f70b, accepted physical pathwise factorial pair 074f945f and second moment equivalence 1a119044. Main pending proof: past intrinsic count adaptedness, monotone dyadic mesh-to-pair identity, source expectation limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_chronological_pair_mean_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      (((T : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by sorry
