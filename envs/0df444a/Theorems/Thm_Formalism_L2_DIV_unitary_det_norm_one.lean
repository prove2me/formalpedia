-- Prove2me | Theorems.Thm_Formalism_L2_DIV_unitary_det_norm_one
-- name    : Formalism.L2.DIV.unitary_det_norm_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:22:46.886595+00:00
-- url     : https://prove2.me/theorems/ea0fd474-ad09-4928-8615-6c3ad0bcba7c
-- title:
--   DIV: unitary det norm one
-- statement:
--   The DIV construction uses the unitary det norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L88-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L88-L97

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

theorem Formalism.L2.DIV.unitary_det_norm_one {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (hJ : IsUnit J.det)
    (g : GL (Fin n) A) (hg : g ∈ UJ σ J) : σ (g : Matrix (Fin n) (Fin n) A).det * (g : Matrix (Fin n) (Fin n) A).det = 1 := by sorry
