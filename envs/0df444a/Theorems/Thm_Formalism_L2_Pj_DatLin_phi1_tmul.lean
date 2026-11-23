-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_phi1_tmul
-- name    : Formalism.L2.Pj.DatLin.phi1_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:13.587797+00:00
-- url     : https://prove2.me/theorems/779a2dd7-5ec1-4ab0-a76e-b14bd3d4bf7a
-- title:
--   Dat Lin: phi1 tmul
-- statement:
--   The Dat Lin construction uses the phi1 tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean#L25-L28

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable (Ψ : Finset (E →+* ℂ))

theorem Formalism.L2.Pj.DatLin.phi1_tmul (x : ℝ) (e : 𝓞 E) :
    phi1 Ψ (x ⊗ₜ e) = fun τ : Ψ => (x : ℂ) * (τ : E →+* ℂ) (e : E) := by sorry
