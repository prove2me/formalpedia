-- Prove2me | Theorems.Thm_Formalism_SLP_P_CountO_index_sup_mulSub_dvd
-- name    : Formalism.SLP.P.CountO.index_sup_mulSub_dvd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:01.077225+00:00
-- url     : https://prove2.me/theorems/a5fc0705-e1ff-4d4c-b8eb-f1e69907b2da
-- title:
--   Count O: index sup mul Sub dvd
-- statement:
--   The Count O construction uses the index sup mul Sub dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L269-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L269-L291

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

theorem Formalism.SLP.P.CountO.index_sup_mulSub_dvd (N : Submodule R X) {a b : ℕ} (hab : a.Coprime b)
    (ha : 0 < a) (hb : 0 < b) (hN : N.toAddSubgroup.index = a * b) :
    (N ⊔ mulSub R X a).toAddSubgroup.index ∣ a := by sorry
