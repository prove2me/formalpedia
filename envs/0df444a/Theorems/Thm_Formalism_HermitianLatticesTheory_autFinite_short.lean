-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_autFinite_short
-- name    : Formalism.HermitianLatticesTheory.autFinite_short
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:38.042964+00:00
-- url     : https://prove2.me/theorems/52eb5eeb-d9a6-4ab2-97d3-37fd5e53e6f9
-- title:
--   Hermitian Lattices Theory: aut Finite short
-- statement:
--   The Hermitian Lattices Theory construction uses the aut Finite short property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/AutFinite.lean#L16-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/AutFinite.lean#L16-L43

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

theorem Formalism.HermitianLatticesTheory.autFinite_short (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) [Submodule.IsLattice K L] (R : ℚ) :
    Set.Finite {v : V | v ∈ L ∧ Algebra.trace ℚ K (h v v) ≤ R} := by sorry
