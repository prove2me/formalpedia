-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_Cay_gram_det_ne_zero
-- name    : Formalism.L2.Th1.H.Cay.gram_det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:48.222796+00:00
-- url     : https://prove2.me/theorems/be202543-a2ea-44b7-a81c-a6e50278c784
-- title:
--   Cay: gram det ne zero
-- statement:
--   The Cay construction uses the gram det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/UnitaryEighthOf.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/UnitaryEighthOf.lean#L18-L35

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_UnitaryEighthOf
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
open Formalism.L2.Th1.H.Cay
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem Formalism.L2.Th1.H.Cay.gram_det_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (H : Sesq V) (hpos : IsPosDef H)
    (e : Module.Basis ι ℂ V) : (Matrix.of fun i j => H (e i) (e j)).det ≠ 0 := by sorry
