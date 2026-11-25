-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_laurent_embedding_injective
-- name    : Formalism.L2.Th1.A.laurent_embedding_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:55.528743+00:00
-- url     : https://prove2.me/theorems/50618879-ed09-5e03-aa31-95d6e5481cd9
-- title:
--   A: laurent embedding injective
-- statement:
--   The A construction uses the laurent embedding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/Laurent.lean#L176-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/Laurent.lean#L176-L178

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.laurent_embedding_injective : ToLInjective.{u} := by sorry
