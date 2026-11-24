-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_blockEmb_C
-- name    : Formalism.L2.DIV.fk_blockEmb_C
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:43.64289+00:00
-- url     : https://prove2.me/theorems/5ab6505f-b0b0-46c7-b1f2-8bb124b9775b
-- title:
--   DIV: fk block Emb C
-- statement:
--   The DIV construction uses the fk block Emb C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L22-L24

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
variable {K : Type} [Field K] [StarRing K] {ι : Type} {n : ℕ}
omit [StarRing K]

theorem Formalism.L2.DIV.fk_blockEmb_C (τ : ι) (a : K) :
    Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ (C a) = (C a : MvPolynomial (ι × Fin n × Fin n) K) := by sorry
