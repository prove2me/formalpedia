-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_theta_bijective
-- name    : Formalism.L2.Pj.DatLin.theta_bijective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:07.364118+00:00
-- url     : https://prove2.me/theorems/e8dfd0d8-4973-49fd-9d2d-b8f9c1c07e99
-- title:
--   Dat Lin: theta bijective
-- statement:
--   The Dat Lin construction uses the theta bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean#L199-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean#L199-L272

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
variable {Ψ}
variable {b M}
variable (b M)

theorem Formalism.L2.Pj.DatLin.theta_bijective (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ)
    (hfg : Module.Finite (𝓞 E) M) (hsm : ∀ v : V, ∃ s ∈ (𝓞 E)⁰, s • v ∈ M) :
    Function.Bijective (theta b Ψ M) := by sorry
