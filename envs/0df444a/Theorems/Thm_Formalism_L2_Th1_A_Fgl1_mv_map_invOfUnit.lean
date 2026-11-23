-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Fgl1_mv_map_invOfUnit
-- name    : Formalism.L2.Th1.A.Fgl1.mv_map_invOfUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:09:58.419321+00:00
-- url     : https://prove2.me/theorems/9b5ffc13-e6f6-4910-a151-50c7e720b9a8
-- title:
--   Fgl1: mv map inv Of Unit
-- statement:
--   The Fgl1 construction uses the mv map inv Of Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L74-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean#L74-L89

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
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
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem Formalism.L2.Th1.A.Fgl1.mv_map_invOfUnit {σ : Type*} (φ : R →+* S) (a : MvPowerSeries σ R) (e : Rˣ) (e' : Sˣ)
    (h : cc a = e) (h' : φ e = e') :
    MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)
      = MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by sorry
