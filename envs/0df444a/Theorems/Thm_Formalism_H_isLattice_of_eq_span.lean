-- Prove2me | Theorems.Thm_Formalism_H_isLattice_of_eq_span
-- name    : Formalism.H.isLattice_of_eq_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:12.255055+00:00
-- url     : https://prove2.me/theorems/0393e0e3-5e08-46e1-b8b1-5cff9f950ce8
-- title:
--   H: is Lattice of eq span
-- statement:
--   The H construction uses the is Lattice of eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/DualLattice.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/DualLattice.lean#L41-L47

import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.H
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V]

theorem Formalism.H.isLattice_of_eq_span {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ V) (L : Submodule ℤ V)
    (h : L = Submodule.span ℤ (Set.range e)) :
    DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by sorry
