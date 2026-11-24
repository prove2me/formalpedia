-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_summable_gauss_of_discrete
-- name    : Formalism.L2.Th1.H.summable_gauss_of_discrete
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:39.601322+00:00
-- url     : https://prove2.me/theorems/41df952d-6810-42d1-b460-d12c84aec9f7
-- title:
--   H: summable gauss of discrete
-- statement:
--   The H construction uses the summable gauss of discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaloisDescentSubspaces.lean#L27-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaloisDescentSubspaces.lean#L27-L53

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.summable_gauss_of_discrete {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : AddSubgroup V) [hd : DiscreteTopology Λ] {a : ℝ} (ha : 0 < a) :
    Summable fun x : Λ => Real.exp (-a * ‖(x : V)‖ ^ 2) := by sorry
