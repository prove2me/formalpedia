-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_Inv_opU_const_mul
-- name    : Formalism.L2.Th1.H.Inv.opU_const_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:51.258675+00:00
-- url     : https://prove2.me/theorems/b620ad7f-8ed9-468c-82ae-33f57485f926
-- title:
--   Inv: op U const mul
-- statement:
--   The Inv construction uses the op U const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L51-L54

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

theorem Formalism.L2.Th1.H.Inv.opU_const_mul (H : Sesq V) (x : V) (c : ℂ) (G : V → ℂ) (z : V) :
    opU H x (fun v => c * G v) z = c * opU H x G z := by sorry
