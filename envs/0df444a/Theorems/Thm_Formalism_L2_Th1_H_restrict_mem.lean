-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_restrict_mem
-- name    : Formalism.L2.Th1.H.restrict_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:58.022124+00:00
-- url     : https://prove2.me/theorems/89669dd2-84ca-4d1c-bef3-2a16e1e914d0
-- title:
--   H: restrict mem
-- statement:
--   The H construction uses the restrict mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/MatrixFormFourfoldBlockFirstBlockEmb.lean#L73-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/MatrixFormFourfoldBlockFirstBlockEmb.lean#L73-L86

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {n : Type*} [Fintype n]

theorem Formalism.L2.Th1.H.restrict_mem (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (hα0 : α 0 = 1)
    {P : (Fin 4 × n → ℂ) → ℂ}
    (hP : P ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ))
    (z₁ : Fin 4 × n → ℂ) (hz₁ : slice 0 z₁ = 0) :
    (fun v => P (z₁ + emb0 v)) ∈ Th (matH h) α Λ := by sorry
