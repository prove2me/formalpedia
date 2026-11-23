-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_dint
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_dint
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:48.883457+00:00
-- url     : https://prove2.me/theorems/143abc9a-e7cf-4e4b-b490-b9e834e13cf3
-- title:
--   Hermitian Lattices Theory: class Set Assembly dint
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly dint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L63-L70

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
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLatticesTheory.classSetAssembly_dint [Module (NumberField.RingOfIntegers K) V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (d : ℕ) (x y : V)
    (hxy : (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K)) :
    ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x y) = z := by sorry
