-- Prove2me | Theorems.Thm_Formalism_L2_DIV_tilde_norm_quotient
-- name    : Formalism.L2.DIV.tilde_norm_quotient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:48.065153+00:00
-- url     : https://prove2.me/theorems/bbcf7a3d-18dd-4f9d-976a-ad910abfa6c9
-- title:
--   DIV: tilde norm quotient
-- statement:
--   The DIV construction uses the tilde norm quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L25-L28

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

theorem Formalism.L2.DIV.tilde_norm_quotient (σ : E →ₐ[F] E) (ξ : Chr F E L) (h : (h90 σ).ker ≤ ξ.ker) (x : (AfE F E)ˣ) :
    tilde σ ξ ⟨h90 σ x, x, rfl⟩ = ξ x := by sorry
