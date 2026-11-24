-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_walInt_mul
-- name    : Formalism.MainNotions.Gaps.CC.Surj.walInt_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:58:34.217616+00:00
-- url     : https://prove2.me/theorems/c6e7c97e-e9b4-44cc-99f4-937777fa0531
-- title:
--   Surj: wal Int mul
-- statement:
--   The Surj construction uses the wal Int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ClassCountWaLat.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ClassCountWaLat.lean#L41-L43

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
omit [DecidableEq n]

theorem Formalism.MainNotions.Gaps.CC.Surj.walInt_mul (S : Subring A) {M N : Matrix n n A} (hM : walInt S M) (hN : walInt S N) :
    walInt S (M * N) := by sorry
