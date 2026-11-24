-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_conj_mem_iff
-- name    : Formalism.L2.Pj.DatLin.conj_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:05.855719+00:00
-- url     : https://prove2.me/theorems/2e76355d-6888-478f-add9-fefa4ad763bb
-- title:
--   Dat Lin: conj mem iff
-- statement:
--   The Dat Lin construction uses the conj mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatTheta.lean#L32-L35

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
variable {Ψ}

theorem Formalism.L2.Pj.DatLin.conj_mem_iff (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ)
    (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ∈ Ψ ↔ σ ∉ Ψ := by sorry
