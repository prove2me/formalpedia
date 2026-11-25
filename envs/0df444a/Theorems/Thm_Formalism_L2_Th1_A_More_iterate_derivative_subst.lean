-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_More_iterate_derivative_subst
-- name    : Formalism.L2.Th1.A.More.iterate_derivative_subst
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:08:29.895508+00:00
-- url     : https://prove2.me/theorems/b983366d-1b50-4927-9604-c525e04a9f0a
-- title:
--   More: iterate derivative subst
-- statement:
--   The More construction uses the iterate derivative subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L49-L58

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
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
open More
open Formalism.L2.Th1.A.More

theorem Formalism.L2.Th1.A.More.iterate_derivative_subst {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
    (n : ℕ) (f : K⟦X⟧) :
    (derivative K)^[n] (f.subst (expSer W)) = ((D W)^[n] f).subst (expSer W) := by sorry
