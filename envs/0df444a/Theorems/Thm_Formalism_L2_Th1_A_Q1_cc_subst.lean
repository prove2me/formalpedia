-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Q1_cc_subst
-- name    : Formalism.L2.Th1.A.Q1.cc_subst
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:26.644574+00:00
-- url     : https://prove2.me/theorems/c4c26329-82e2-4898-8968-e1aa3d05d7fc
-- title:
--   Q1: cc subst
-- statement:
--   The Q1 construction uses the cc subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/DifferenceLinearCoeff.lean#L34-L40

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_DifferenceLinearCoeff
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_cc_subst

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
open Formalism.L2.Th1.A.Q1
open CubeR
local notation "cc" => MvPowerSeries.constantCoeff
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.Q1.cc_subst {σ τ : Type*} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (ha' : ∀ i, cc (a i) = 0) (f : MvPowerSeries σ R) : cc (f.subst a) = cc f := by sorry
