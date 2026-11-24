-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_qsmul_right
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_tr_qsmul_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:21.725853+00:00
-- url     : https://prove2.me/theorems/3c358744-9016-479c-a942-23bfb299c5b1
-- title:
--   Hermitian Lattices Theory: class Set Assembly tr qsmul right
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly tr qsmul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L40-L42

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_tr_qsmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (q : ℚ) (x y : V) :
    Algebra.trace ℚ K (h x ((q : K) • y)) = q * Algebra.trace ℚ K (h x y) := by sorry
