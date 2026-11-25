-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_More_iterate_D_mem
-- name    : Formalism.L2.Th1.A.More.iterate_D_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:13:51.363495+00:00
-- url     : https://prove2.me/theorems/6d6034f5-edc2-59dd-b1dd-2b939c418bba
-- title:
--   More: iterate D mem
-- statement:
--   The More construction uses the iterate D mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/ChainRuleFormalGroupVar.lean#L116-L122

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
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (S : Subring K)

theorem Formalism.L2.Th1.A.More.iterate_D_mem (hw : ∀ n, coeff n (fw W) ∈ S) (k : ℕ) (f : K⟦X⟧)
    (hf : ∀ n, coeff n f ∈ S) (n : ℕ) : coeff n ((D W)^[k] f) ∈ S := by sorry
