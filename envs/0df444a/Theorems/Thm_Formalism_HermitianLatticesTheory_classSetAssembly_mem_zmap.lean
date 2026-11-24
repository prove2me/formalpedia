-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_mem_zmap
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_mem_zmap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:06.566322+00:00
-- url     : https://prove2.me/theorems/2e18f297-6ee9-4f41-a614-235d1d178805
-- title:
--   Hermitian Lattices Theory: class Set Assembly mem zmap
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly mem zmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L513-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L513-L516

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_mem_zmap {n : ℕ} (ι : V →+ EuclideanSpace ℝ (Fin n))
    (M : Submodule (NumberField.RingOfIntegers K) V) (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ zmap ι M ↔ ∃ x ∈ M, ι x = v := by sorry
