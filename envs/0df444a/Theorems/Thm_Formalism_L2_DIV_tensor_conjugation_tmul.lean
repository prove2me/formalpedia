-- Prove2me | Theorems.Thm_Formalism_L2_DIV_tensor_conjugation_tmul
-- name    : Formalism.L2.DIV.tensor_conjugation_tmul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:45.201902+00:00
-- url     : https://prove2.me/theorems/5c1d7095-bb6c-4e9a-bdd2-2a5c5f18067d
-- title:
--   DIV: tensor conjugation tmul
-- statement:
--   The DIV construction uses the tensor conjugation tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L31-L33

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

theorem Formalism.L2.DIV.tensor_conjugation_tmul (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) (r : R) :
    sigR σ R (e ⊗ₜ[F] r) = σ e ⊗ₜ[F] r := by sorry
