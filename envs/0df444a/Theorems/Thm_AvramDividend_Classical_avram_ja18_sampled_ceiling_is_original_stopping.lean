-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_sampled_ceiling_is_original_stopping
-- name    : AvramDividend.Classical.avram_ja18_sampled_ceiling_is_original_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:35:24.81236+00:00
-- url     : https://prove2.me/theorems/7785f280-77c0-45a1-8693-cf5753d0fe13
-- title:
--   An adapted sampled clock ceiling is a stopping time of the original continuous-time filtration
-- statement:
--   If the original sampled grid index K has level events {K≤i} measurable at the corresponding original right-continuous filtration times e_i, then the random grid time e_(K) is itself a true original right-continuous stopping time. Its event {e_K≤t} is the countable union of events {K≤i,e_i≤t}. No process representation is assumed.
-- source:
--   Needed to turn Proved 1d01e41f sampled stopping indices into real-time upper-clock approximations for 40599988 and therefore 2d92580d. Source-exact countable-union event argument.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_sampled_ceiling_is_original_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (K : Ω → ℕ)
    (hEvents : ∀ i, MeasurableSet[𝓕.rightCont (e i)]
      {ω : Ω | K ω ≤ i}) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => (e (K ω) : WithTop ℝ≥0)) := by sorry
