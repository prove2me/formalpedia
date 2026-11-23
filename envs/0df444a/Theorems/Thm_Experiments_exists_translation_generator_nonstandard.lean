-- Prove2me | Theorems.Thm_Experiments_exists_translation_generator_nonstandard
-- name    : Experiments.exists_translation_generator_nonstandard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:30:54.25111+00:00
-- url     : https://prove2.me/theorems/0a29ad19-49a1-42e5-8aa3-3165b6fe85c8
-- title:
--   Experiments: exists translation generator nonstandard
-- statement:
--   The Experiments construction uses the exists translation generator nonstandard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Translation.lean#L32-L40
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/Translation.lean#L32-L40

import Definitions.Def_Experiments_FiniteDifferenceSemigroup
import Definitions.Def_Experiments_NonstandardSemigroup
import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_Experiments_Translation
set_option autoImplicit true
open Experiments
open KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace

theorem Experiments.exists_translation_generator_nonstandard (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ a : translateSpan ψ →L[ℂ] translateSpan ψ,
      ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • a) := by sorry
