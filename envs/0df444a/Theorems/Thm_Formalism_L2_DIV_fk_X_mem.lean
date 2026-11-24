-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_X_mem
-- name    : Formalism.L2.DIV.fk_X_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:47.861113+00:00
-- url     : https://prove2.me/theorems/20ba91ca-11db-450f-97eb-1c26f2a0f0cc
-- title:
--   DIV: fk X mem
-- statement:
--   The DIV construction uses the fk X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L114-L115

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

theorem Formalism.L2.DIV.fk_X_mem {σ : Type} (v : σ) : (X v : MvPolynomial σ K) ∈ (map (σ := σ) K0.subtype).range := by sorry
