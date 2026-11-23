-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_Inv_opU_finset_sum
-- name    : Formalism.L2.Th1.H.Inv.opU_finset_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:20.160672+00:00
-- url     : https://prove2.me/theorems/26881229-9129-44ca-8cb0-b962ac401a3d
-- title:
--   Inv: op U finset sum
-- statement:
--   The Inv construction uses the op U finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/LogarithmEquivalence.lean#L56-L58

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

theorem Formalism.L2.Th1.H.Inv.opU_finset_sum {ι : Type} (H : Sesq V) (x : V) (S : Finset ι) (G : ι → V → ℂ) (z : V) :
    opU H x (fun v => ∑ i ∈ S, G i v) z = ∑ i ∈ S, opU H x (G i) z := by sorry
