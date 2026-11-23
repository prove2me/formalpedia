-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_Inv_int_of_exp_two_pi
-- name    : Formalism.L2.Th1.H.Inv.int_of_exp_two_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:38.242826+00:00
-- url     : https://prove2.me/theorems/e6954e4d-1678-47c0-8a98-b68cd49ad52b
-- title:
--   Inv: int of exp two pi
-- statement:
--   The Inv construction uses the int of exp two pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L29-L39

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

theorem Formalism.L2.Th1.H.Inv.int_of_exp_two_pi {t : ℝ}
    (h : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (t : ℂ)) = 1) : ∃ m : ℤ, t = (m : ℝ) := by sorry
