-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_lemma_18
-- name    : BulteauTranspositions.NPHard.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:53:50.272226+00:00
-- url     : https://prove2.me/theorems/e378713c-296e-4292-a913-70b60ec7d342
-- title:
--   Lemma 18 — valid contexts persist and finish collapsing
-- statement:
--   Let (I′,B′) be obtained from an assembling of basic blocks (I,B) after any finite number of 3DT-steps, including zero steps. Then (I′,B′) is a valid context. Moreover, if its variable set is empty, I′ is 3DT-collapsible. Validity along the run is a conclusion, not an assumption.
--
--   Differences from the source:
--   - encoding: finite alphabets and a set of disjoint oriented triples → natural-number symbol names and a list of triples with a duplicate-free flattened alphabet; reason: finite alphabets admit injective naming; triple list order has no operational significance
--   - encoding: a set partition of external triples and an l-block decomposition → lists with exact membership and no duplicates, and cuts whose final endpoint is the span; reason: list order is auxiliary; block numbering and occupied-symbol order agree with the source
--   - encoding: the remaining variable set is empty → every remaining triple is internal; reason: in the valid-context conclusion, variables partition exactly the external triples; either condition says that this partition is empty
--   - encoding: assemblings with arbitrary symbol names → canonical gate lists up to an injective relabeling and permutation of the triple list; reason: the four words and exact one-source/one-target incidence conditions give all assemblings of Definition 14
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Lemma 18, printed p. 21 = PDF p. 21; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Blocks

namespace BulteauTranspositions.NPHard

theorem lemma_18 (C D : Context) (hC : IsAssembly C) (hrun : ContextRun C D) :
    ValidContext D ∧
      ((∀ t ∈ D.inst.triples, Internal D t) → Collapsible D.inst) := by sorry

end BulteauTranspositions.NPHard
