-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_weylRel_end_bar
-- name    : Formalism.QuantumDeterminants.weylRel_end_bar
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:01.519181+00:00
-- url     : https://prove2.me/theorems/47beef3d-bd09-49c9-8973-24cce623092b
-- title:
--   Quantum Determinants: weyl Rel end bar
-- statement:
--   The Quantum Determinants construction uses the weyl Rel end bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FinalWR.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FinalWR.lean#L44-L52

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.weylRel_end_bar (l : Fin m) :
    Formalism.YangianSpanCharacter.T.WeylRel (pbEnd (E := E) l) (cbEnd l) (cbiEnd l) := by sorry
