-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_form_of_diag
-- name    : Formalism.L2.Th1.H.form_of_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:52.722808+00:00
-- url     : https://prove2.me/theorems/0216d7f8-3f39-49ed-b5e5-e418baf97685
-- title:
--   H: form of diag
-- statement:
--   The H construction uses the form of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyIdentity.lean#L118-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyIdentity.lean#L118-L130

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.form_of_diag {n : Type*} [Fintype n] [DecidableEq n] (H : Sesq V) (b : Module.Basis n ℂ V) (l : n → ℂ)
    (L : V →ₗ[ℂ] V) (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (hL : ∀ i, L (b i) = l i • b i)
    (w : n → ℂ) :
    H (L (b.equivFun.symm w)) (b.equivFun.symm w) = ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2 := by sorry
