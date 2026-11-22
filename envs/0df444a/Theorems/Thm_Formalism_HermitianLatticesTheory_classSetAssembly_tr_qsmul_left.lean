-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_qsmul_left
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_tr_qsmul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:57.123581+00:00
-- url     : https://prove2.me/theorems/30ad0718-e90a-4401-8786-fca09697bc41
-- title:
--   Hermitian Lattices Theory: class Set Assembly tr qsmul left
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly tr qsmul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L34-L38

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_tr_qsmul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (q : ℚ) (x y : V) :
    Algebra.trace ℚ K (h ((q : K) • x) y) = q * Algebra.trace ℚ K (h x y) := by sorry
