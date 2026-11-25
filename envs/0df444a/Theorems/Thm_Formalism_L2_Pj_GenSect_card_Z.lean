-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_card_Z
-- name    : Formalism.L2.Pj.GenSect.card_Z
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:32:58.787513+00:00
-- url     : https://prove2.me/theorems/78363335-58c6-41f1-bc5f-23e64d7ab3ac
-- title:
--   Gen Sect: card Z
-- statement:
--   The Gen Sect construction uses the card Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L76-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L76-L87

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial Cardinal
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem Formalism.L2.Pj.GenSect.card_Z (j₀ : Fin m) : Fintype.card {p : Fin (D + 1) × Fin m // Zs j₀ p} = D := by sorry
