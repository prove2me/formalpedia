-- Prove2me | Theorems.Thm_Experiments_eq_exp_of_sequence_generator
-- name    : Experiments.eq_exp_of_sequence_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:16.96594+00:00
-- url     : https://prove2.me/theorems/b76dcbdd-99a2-4084-88ca-4aec5934532a
-- title:
--   Experiments: eq exp of sequence generator
-- statement:
--   The Experiments construction uses the eq exp of sequence generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/FiniteDifferenceSemigroup.lean#L64-L109
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/FiniteDifferenceSemigroup.lean#L64-L109

import Definitions.Def_Experiments_GeneratorBound
import Definitions.Def_Experiments_FiniteDifferenceSemigroup
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem Experiments.eq_exp_of_sequence_generator (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    (a : A) (h : ℕ → ℝ) (hpos : ∀ n, 0 < h n)
    (hz : Tendsto h atTop (𝓝 0))
    (ha : Tendsto (fun n => (h n)⁻¹ • (M (h n) - 1)) atTop (𝓝 a)) :
    ∀ t, 0 ≤ t → M t = exp (t • a) := by sorry
