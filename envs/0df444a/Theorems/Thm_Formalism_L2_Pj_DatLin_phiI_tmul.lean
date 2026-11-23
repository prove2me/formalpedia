-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_phiI_tmul
-- name    : Formalism.L2.Pj.DatLin.phiI_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:56.480209+00:00
-- url     : https://prove2.me/theorems/42ff55e6-89f5-44ec-a7c8-50de2188fc3c
-- title:
--   Dat Lin: phi I tmul
-- statement:
--   The Dat Lin construction uses the phi I tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean#L116-L119

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
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis ι E V) (Ψ : Finset (E →+* ℂ)) (M : Submodule (𝓞 E) V)

theorem Formalism.L2.Pj.DatLin.phiI_tmul (x : ℝ) (n : ι → 𝓞 E) :
    phiI Ψ (x ⊗ₜ n) = fun (τ : Ψ) i => (x : ℂ) * (τ : E →+* ℂ) (n i : E) := by sorry
