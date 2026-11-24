-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_blockEmb_X
-- name    : Formalism.L2.DIV.fk_blockEmb_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:42.323102+00:00
-- url     : https://prove2.me/theorems/b4c8cfd9-2198-4c3c-a996-223966b6f27f
-- title:
--   DIV: fk block Emb X
-- statement:
--   The DIV construction uses the fk block Emb X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L17-L19

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

theorem Formalism.L2.DIV.fk_blockEmb_X (τ : ι) (v : Fin n × Fin n) :
    Formalism.GradedWeylDivisibility.blockEmb K τ (X v) = (X (τ, v) : MvPolynomial (ι × Fin n × Fin n) K) := by sorry
