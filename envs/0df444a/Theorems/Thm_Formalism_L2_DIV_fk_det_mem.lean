-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_det_mem
-- name    : Formalism.L2.DIV.fk_det_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:16.073923+00:00
-- url     : https://prove2.me/theorems/b331dbfb-a0ae-418f-9688-f705e0fc5b1e
-- title:
--   DIV: fk det mem
-- statement:
--   The DIV construction uses the fk det mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L132-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L132-L138

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

theorem Formalism.L2.DIV.fk_det_mem {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (hG : ∀ a b, G a b ∈ K0) : G.det ∈ K0 := by sorry
