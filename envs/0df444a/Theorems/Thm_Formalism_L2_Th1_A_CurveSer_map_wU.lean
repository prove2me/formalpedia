-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_wU
-- name    : Formalism.L2.Th1.A.CurveSer.map_wU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:55.323565+00:00
-- url     : https://prove2.me/theorems/c39c25d2-7412-4748-8d0a-e84abe7f9577
-- title:
--   Curve Ser: map w U
-- statement:
--   The Curve Ser construction uses the map w U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L154-L156

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

theorem Formalism.L2.Th1.A.CurveSer.map_wU : PowerSeries.map φ (wU W) = wU (W.map φ) := by sorry
