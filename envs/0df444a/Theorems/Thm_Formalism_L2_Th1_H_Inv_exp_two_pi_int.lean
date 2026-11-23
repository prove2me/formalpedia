-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_Inv_exp_two_pi_int
-- name    : Formalism.L2.Th1.H.Inv.exp_two_pi_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:30.393807+00:00
-- url     : https://prove2.me/theorems/842c1934-8c42-47c1-8907-4c7a6a7357ed
-- title:
--   Inv: exp two pi int
-- statement:
--   The Inv construction uses the exp two pi int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L23-L27

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

theorem Formalism.L2.Th1.H.Inv.exp_two_pi_int (m : ℤ) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((m : ℝ)) : ℂ)) = 1 := by sorry
