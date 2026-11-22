-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_tr_sum_left
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_tr_sum_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:28.076604+00:00
-- url     : https://prove2.me/theorems/a8b84961-4ca2-4fe7-9b4f-8d1a2a322e1b
-- title:
--   Hermitian Lattices Theory: class Set Assembly tr sum left
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly tr sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L44-L47

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_tr_sum_left (h : V →ₗ⋆[K] V →ₗ[K] K) {ι : Type*} (s : Finset ι)
    (f : ι → V) (y : V) :
    Algebra.trace ℚ K (h (∑ i ∈ s, f i) y) = ∑ i ∈ s, Algebra.trace ℚ K (h (f i) y) := by sorry
