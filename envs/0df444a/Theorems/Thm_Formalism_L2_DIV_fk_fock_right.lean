-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_fock_right
-- name    : Formalism.L2.DIV.fk_fock_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:16.32364+00:00
-- url     : https://prove2.me/theorems/2c6aada4-d361-4181-8274-a4e99cc71e0e
-- title:
--   DIV: fk fock right
-- statement:
--   The DIV construction uses the fk fock right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L42-L51

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

theorem Formalism.L2.DIV.fk_fock_right (τ : ι) (P Q : MvPolynomial (ι × Fin n × Fin n) K) (hP : ∀ v, pderiv (τ, v) P = 0)
    (g : MvPolynomial (Fin n × Fin n) K) :
    fockL P (Formalism.GradedWeylDivisibility.blockEmb K τ g * Q) = constantCoeff g * fockL P Q := by sorry
