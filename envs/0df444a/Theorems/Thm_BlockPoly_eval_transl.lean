-- Prove2me | Theorems.Thm_BlockPoly_eval_transl
-- name    : BlockPoly.eval_transl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:24.555919+00:00
-- url     : https://prove2.me/theorems/7fea2413-8221-4bde-9b22-58cd9eec3c7f
-- title:
--   Block Poly: eval transl
-- statement:
--   The Block Poly construction uses the eval transl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L180-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/MapDomainMemOfDvd.lean#L180-L195

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open BlockPoly
open MvPolynomial
variable {K : Type*} [Field K] {D N : ℕ}

theorem BlockPoly.eval_transl (z : Fin (D + 1) × Fin (N + 1) → K)
    (f : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K) :
    eval (fun t => if t.1 = 0 then 0 else z t) (transl (fun j => z (0, j)) f) = eval z f := by sorry
