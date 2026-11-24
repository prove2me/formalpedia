-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_finite_rat
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_finite_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:40.809963+00:00
-- url     : https://prove2.me/theorems/94772dec-fa19-4453-aac6-720a7db766f0
-- title:
--   Hermitian Lattices Theory: class Set Assembly finite rat
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly finite rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L246-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L246-L269

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_finite_rat (d : ℕ) (hd : 0 < d) (R : ℝ) :
    {q : ℚ | (∃ z : ℤ, (d : ℚ) * q = z) ∧ |(q : ℝ)| ≤ R}.Finite := by sorry
