-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_extNorm_mem
-- name    : Formalism.L2.DIV.fk_extNorm_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:05.762835+00:00
-- url     : https://prove2.me/theorems/f4e3cde7-108b-4457-a2be-c309d2d9abc7
-- title:
--   DIV: fk ext Norm mem
-- statement:
--   The DIV construction uses the fk ext Norm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L147-L151

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] (K0 : Subfield K)

theorem Formalism.L2.DIV.fk_extNorm_mem [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) : extNorm K lam ∈ K0 := by sorry
