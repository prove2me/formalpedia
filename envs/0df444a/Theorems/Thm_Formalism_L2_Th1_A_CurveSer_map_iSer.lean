-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_iSer
-- name    : Formalism.L2.Th1.A.CurveSer.map_iSer
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:41.825906+00:00
-- url     : https://prove2.me/theorems/1b75e550-54ef-432d-be62-66f1d8221c1c
-- title:
--   Curve Ser: map i Ser
-- statement:
--   The Curve Ser construction uses the map i Ser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L194-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L194-L198

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.CurveSer
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {S : Type v} [CommRing S] (φ : R →+* S)

theorem Formalism.L2.Th1.A.CurveSer.map_iSer : PowerSeries.map φ (iSer W) = iSer (W.map φ) := by sorry
