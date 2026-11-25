-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_add_right
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_tr_add_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:48:52.979694+00:00
-- url     : https://prove2.me/theorems/0442ff24-96fa-5c42-bb44-766453743a82
-- title:
--   Hermitian Lattices Theory: class Set Assembly tr add right
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly tr add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L24-L26

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_tr_add_right (h : V →ₗ⋆[K] V →ₗ[K] K) (x y z : V) :
    Algebra.trace ℚ K (h z (x + y)) = Algebra.trace ℚ K (h z x) + Algebra.trace ℚ K (h z y) := by sorry
