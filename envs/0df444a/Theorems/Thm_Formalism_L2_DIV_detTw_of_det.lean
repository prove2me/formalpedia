-- Prove2me | Theorems.Thm_Formalism_L2_DIV_detTw_of_det
-- name    : Formalism.L2.DIV.detTw_of_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:31.868084+00:00
-- url     : https://prove2.me/theorems/b11a4d30-6d56-49dd-ae04-acc2b13f0ccf
-- title:
--   DIV: det Tw of det
-- statement:
--   The DIV construction uses the det Tw of det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L30-L36

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem Formalism.L2.DIV.detTw_of_det (σ : E →ₐ[F] E) (ξ : Chr F E L) (h : (h90 σ).ker ≤ ξ.ker) {n : ℕ}
    (g : GL (Fin n) (AfE F E)) (x : (AfE F E)ˣ) (hx : h90 σ x = Matrix.GeneralLinearGroup.det g) :
    detTw σ ξ g = ξ x := by sorry
