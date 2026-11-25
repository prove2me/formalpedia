-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_trdeg_CT
-- name    : Formalism.L2.Pj.GenSect.trdeg_CT
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:30:11.117824+00:00
-- url     : https://prove2.me/theorems/16139975-335d-4f12-8b55-2ed093f72091
-- title:
--   Gen Sect: trdeg CT
-- statement:
--   The Gen Sect construction uses the trdeg CT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L89-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L89-L98

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

theorem Formalism.L2.Pj.GenSect.trdeg_CT (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D) :
    Algebra.trdeg K (CT Ω D j₀) = (Fintype.card (Fin (D + 1) × Fin m) : Cardinal) := by sorry
