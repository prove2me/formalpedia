-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_walInt_sub
-- name    : Formalism.MainNotions.Gaps.CC.Surj.walInt_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:57:29.897547+00:00
-- url     : https://prove2.me/theorems/c850079d-0890-467f-8aea-3a913ff6f58b
-- title:
--   Surj: wal Int sub
-- statement:
--   The Surj construction uses the wal Int sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ClassCountWaLat.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ClassCountWaLat.lean#L51-L53

import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ClassCountWaLat
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.CC Formalism.MainNotions.Gaps.CC.Surj
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n]

theorem Formalism.MainNotions.Gaps.CC.Surj.walInt_sub (S : Subring A) {M N : Matrix n n A} (hM : walInt S M) (hN : walInt S N) :
    walInt S (M - N) := by sorry
