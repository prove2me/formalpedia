-- Prove2me | Theorems.Thm_Formalism_L2_DIV_d_finrank_of_conj
-- name    : Formalism.L2.DIV.d_finrank_of_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:45:04.046353+00:00
-- url     : https://prove2.me/theorems/b564cb00-fa3e-42f1-bd3f-30a89453fbd7
-- title:
--   DIV: d finrank of conj
-- statement:
--   The DIV construction uses the d finrank of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1655-L1699
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L1655-L1699

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

theorem Formalism.L2.DIV.d_finrank_of_conj {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsConjOf σ) : Module.finrank F E = 2 := by sorry
