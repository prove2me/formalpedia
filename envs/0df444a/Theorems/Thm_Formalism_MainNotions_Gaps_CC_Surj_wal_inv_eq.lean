-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_CC_Surj_wal_inv_eq
-- name    : Formalism.MainNotions.Gaps.CC.Surj.wal_inv_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:57:40.080022+00:00
-- url     : https://prove2.me/theorems/ae0b0264-3131-43c1-bbbc-b846be4bc318
-- title:
--   Surj: wal inv eq
-- statement:
--   The Surj construction uses the wal inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ClassCountWaLat.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ClassCountWaLat.lean#L72-L82

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

theorem Formalism.MainNotions.Gaps.CC.Surj.wal_inv_eq (τ : A →+* A) (J Ji : Matrix n n A) (hJi : Ji * J = 1) (u : GL n A)
    (hu : u ∈ UJ τ J) :
    ((u⁻¹ : GL n A) : Matrix n n A) = Ji * cT τ (u : Matrix n n A) * J := by sorry
