-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fk_fock_mul
-- name    : Formalism.L2.DIV.fk_fock_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:18.744344+00:00
-- url     : https://prove2.me/theorems/28ca6f30-9759-4f4e-83e2-42fcf3199d12
-- title:
--   DIV: fk fock mul
-- statement:
--   The DIV construction uses the fk fock mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/CoefficientsModP/FkPderivBlockEmbNe.lean#L53-L65

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

theorem Formalism.L2.DIV.fk_fock_mul (τ : ι) (P P' : MvPolynomial (ι × Fin n × Fin n) K) (hP : ∀ v, pderiv (τ, v) P = 0)
    (hP' : ∀ v, pderiv (τ, v) P' = 0) (f g : MvPolynomial (Fin n × Fin n) K) :
    fockL (Formalism.GradedWeylDivisibility.blockEmb K τ f * P) (Formalism.GradedWeylDivisibility.blockEmb K τ g * P') = fockL f g * fockL P P' := by sorry
