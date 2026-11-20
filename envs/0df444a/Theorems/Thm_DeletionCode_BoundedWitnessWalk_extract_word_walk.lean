-- Prove2me | Theorems.Thm_DeletionCode_BoundedWitnessWalk_extract_word_walk
-- name    : DeletionCode.BoundedWitnessWalk.extract_word_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:32:53.689147+00:00
-- url     : https://prove2.me/theorems/e1615f41-5318-4df2-b61c-806cae800c94
-- title:
--   Bounded Witness Walk: extract word walk
-- statement:
--   For a walk of actual k-unique words, Boolean spectra are a consequence of
--   the checked path lemma. Only the edge catalogue/survival interface remains.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BoundedWitnessWalk.lean#L84-L121
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BoundedWitnessWalk.lean#L84-L121

import Definitions.Def_DeletionCode_WitnessCases
import Definitions.Def_DeletionCode_FiniteWalkRules
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_BoundedWitnessWalk
set_option autoImplicit true
open DeletionCode DeletionCode.BoundedWitnessWalk
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open CatalogueAlgebra FiniteWalkRules WalkSelection BlockPartition WitnessCases

theorem DeletionCode.BoundedWitnessWalk.extract_word_walk {t k m n : ℕ} (ht : 2 ≤ t)
    (words : Fin (m + 1) → Letters)
    (K : Set (Gram (windowLength k) → ℤ))
    (hunique : ∀ j, Windows.KUnique (words j) n k)
    (hclosed : Agree (words 0) 0 (words (Fin.last m)) 0 n) (hodd : Odd m)
    (hcat : ∀ i : Fin m, CatalogueRule t k
      (wordSpectrum (words i.succ) n (windowLength k) -
       wordSpectrum (words i.castSucc) n (windowLength k)))
    (hK : ∀ i : Fin m, (wordSpectrum (words i.succ) n (windowLength k) -
       wordSpectrum (words i.castSucc) n (windowLength k)) ∈ K) :
    ∃ U : RuleSet k,
      Witness t k (wordSpectrum (words 0) n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t (words 0) n k U.card (componentCount U) U := by sorry
