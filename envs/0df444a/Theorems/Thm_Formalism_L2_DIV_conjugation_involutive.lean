-- Prove2me | Theorems.Thm_Formalism_L2_DIV_conjugation_involutive
-- name    : Formalism.L2.DIV.conjugation_involutive
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:22:18.853079+00:00
-- url     : https://prove2.me/theorems/b5126b24-c76e-41ce-8eaf-bc3a9d01a753
-- title:
--   DIV: conjugation involutive
-- statement:
--   The DIV construction uses the conjugation involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L35-L40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem Formalism.L2.DIV.conjugation_involutive (σ : E →ₐ[F] E) (hσ : IsConjOf σ) (R : Type) [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    sigR σ R (sigR σ R z) = z := by sorry
