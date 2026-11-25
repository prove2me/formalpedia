-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenSect_isAlgebraic_map_adjoin
-- name    : Formalism.L2.Pj.GenSect.isAlgebraic_map_adjoin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:33:03.288811+00:00
-- url     : https://prove2.me/theorems/6c14558c-877e-4302-9171-d5a7eea37a51
-- title:
--   Gen Sect: is Algebraic map adjoin
-- statement:
--   The Gen Sect construction uses the is Algebraic map adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L100-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSectB.lean#L100-L114

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

theorem Formalism.L2.Pj.GenSect.isAlgebraic_map_adjoin {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (hφ : Function.Injective φ) (s : Set A) {a : A}
    (h : IsAlgebraic (Algebra.adjoin R s) a) : IsAlgebraic (Algebra.adjoin R (φ '' s)) (φ a) := by sorry
