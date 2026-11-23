-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_sub_left
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_tr_sub_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:20.431479+00:00
-- url     : https://prove2.me/theorems/46c88e71-b2c9-418f-8f0f-ea3359ee1109
-- title:
--   Hermitian Lattices Theory: class Set Assembly tr sub left
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly tr sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L20-L22

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_tr_sub_left (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h (x - y) z) = Algebra.trace ℚ K (h x z) - Algebra.trace ℚ K (h y z) := by sorry
