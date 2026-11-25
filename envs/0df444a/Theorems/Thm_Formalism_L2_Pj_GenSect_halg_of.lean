-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_halg_of
-- name    : Formalism.L2.Pj.GenSect.halg_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:32:56.031397+00:00
-- url     : https://prove2.me/theorems/db942874-3efe-4e02-bf62-3929791b887b
-- title:
--   Gen Sect: halg of
-- statement:
--   The Gen Sect construction uses the halg of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L248-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L248-L263

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

theorem Formalism.L2.Pj.GenSect.halg_of (x : Fin m → Ω) (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω := by sorry
