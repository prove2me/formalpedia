-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_Inv_inter_smul
-- name    : Formalism.L2.Th1.H.Inv.inter_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:32.802243+00:00
-- url     : https://prove2.me/theorems/9c2c65f1-a721-42c1-8202-8d0e4552737d
-- title:
--   Inv: inter smul
-- statement:
--   The Inv construction uses the inter smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L135-L144

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
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
open Formalism.L2.Th1.H.Inv
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.Inv.inter_smul (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V) (c : ℂ) (F : V → ℂ) :
    inter H α Λ₁ Λ₂ (c • F) = c • inter H α Λ₁ Λ₂ F := by sorry
