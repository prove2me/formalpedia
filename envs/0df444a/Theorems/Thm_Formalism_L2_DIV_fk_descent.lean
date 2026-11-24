-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_descent
-- name    : Formalism.L2.DIV.fk_descent
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:36.288513+00:00
-- url     : https://prove2.me/theorems/c3bd1d9b-a134-43dd-97a8-582ffe903ad2
-- title:
--   DIV: fk descent
-- statement:
--   The DIV construction uses the fk descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L158-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L158-L188

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

theorem Formalism.L2.DIV.fk_descent {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ K) (hv : LinearIndependent K v)
    (hv0 : ∀ i, v i ∈ (map (σ := σ) K0.subtype).range) (c : κ → K)
    (hx : ∑ i, c i • v i ∈ (map (σ := σ) K0.subtype).range) (i : κ) : c i ∈ K0 := by sorry
