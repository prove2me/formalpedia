-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_der_three_mul
-- name    : Formalism.L2.Th1.A.der_three_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:08.389328+00:00
-- url     : https://prove2.me/theorems/3b19351d-6375-4535-bdb8-da4a89bd937f
-- title:
--   A: der three mul
-- statement:
--   The A construction uses the der three mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowTrans.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FlowTrans.lean#L25-L27

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {A : Type u} [CommRing A]

theorem Formalism.L2.Th1.A.der_three_mul (d : Derivation ℤ A A) (a : A) : d (3 * a) = 3 * d a := by sorry
