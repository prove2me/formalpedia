-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_CurveSer_map_invOfUnit
-- name    : Formalism.L2.Th1.A.CurveSer.map_invOfUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:39.500291+00:00
-- url     : https://prove2.me/theorems/293b6444-41da-4abf-96be-8b0252fef91a
-- title:
--   Curve Ser: map inv Of Unit
-- statement:
--   The Curve Ser construction uses the map inv Of Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/CurveSer.lean#L17-L31

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
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem Formalism.L2.Th1.A.CurveSer.map_invOfUnit (φ : R →+* S) (a : R⟦X⟧) (e : Rˣ) (h : constantCoeff a = e) :
    PowerSeries.map φ (invOfUnit a e) = invOfUnit (PowerSeries.map φ a) (Units.map φ e) := by sorry
