-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_generic_indep_pair_random_Ico_mark_shift
-- name    : AvramDividend.Classical.avram_a06_generic_indep_pair_random_Ico_mark_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:33:16.538168+00:00
-- url     : https://prove2.me/theorems/e5d9cbe4-0a87-4782-b572-bffb54235a7b
-- title:
--   Independent random index pair and stationary mark stream yield law invariant random finite block
-- statement:
--   Under an arbitrary probability law, an almost-everywhere-measurable Nat-valued pair independent of a full mark stream and invariant deterministic shifts of the mark stream imply that the random interval mark sum has the same law as a fresh prefix of equal random length.
-- source:
--   Use indepFun_iff_map_prod_eq_prod_map_map, reduce random count pair to product law; on each fixed pair (a,b), reindex sum_Ico as prefix of shift_a M; deterministic shift invariance makes the mark distribution identical. Prove equality of pushforward measures by Fubini and measurable countable partition into Nat pairs. This is the precise missing generic conditional-law step in original marked-band stationarity.

import Mathlib
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_generic_indep_pair_random_Ico_mark_shift
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → Fin 2 → ℕ) (M : Ω → ℕ → ℝ)
    (hN : AEMeasurable N P)
    (hM : AEMeasurable M P)
    (hNM : IndepFun N M P)
    (hshift : ∀ m : ℕ,
      IdentDistrib (fun ω j => M ω (m + j)) M P P) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.Ico (N ω 0) (N ω 1), M ω j)
      (fun ω => ∑ j ∈ Finset.range (N ω 1 - N ω 0), M ω j) P P := by sorry
