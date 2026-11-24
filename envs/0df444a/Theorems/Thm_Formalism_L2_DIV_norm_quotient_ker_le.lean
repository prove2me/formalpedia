-- Prove2me | Theorems.Thm_Formalism_L2_DIV_norm_quotient_ker_le
-- name    : Formalism.L2.DIV.norm_quotient_ker_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:16.14492+00:00
-- url     : https://prove2.me/theorems/e779ea00-af9a-4748-b166-777669331c89
-- title:
--   DIV: norm quotient ker le
-- statement:
--   The DIV construction uses the norm quotient ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/DivisibilityProofs/TuplesP.lean#L166-L168

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

theorem Formalism.L2.DIV.norm_quotient_ker_le {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
    (σ : E →ₐ[F] E) (ξ : Chr F E L) (hσ : IsConjOf σ) (hξ : (idF F E).range ≤ ξ.ker) : (h90 σ).ker ≤ ξ.ker := by sorry
