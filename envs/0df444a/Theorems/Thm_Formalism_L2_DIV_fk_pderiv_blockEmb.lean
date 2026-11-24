-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_pderiv_blockEmb
-- name    : Formalism.L2.DIV.fk_pderiv_blockEmb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:01.55041+00:00
-- url     : https://prove2.me/theorems/71309b65-4c7f-46da-98b8-5fd92647956c
-- title:
--   DIV: fk pderiv block Emb
-- statement:
--   The DIV construction uses the fk pderiv block Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L27-L30

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

theorem Formalism.L2.DIV.fk_pderiv_blockEmb (τ : ι) (v : Fin n × Fin n) (g : MvPolynomial (Fin n × Fin n) K) :
    pderiv (τ, v) (Formalism.GradedWeylDivisibility.blockEmb K τ g) = Formalism.GradedWeylDivisibility.blockEmb K τ (pderiv v g) := by sorry
