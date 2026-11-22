-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_ratCast_mul
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_ratCast_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:24.233944+00:00
-- url     : https://prove2.me/theorems/8d8836fe-8b95-4397-ae31-96d213b5adc2
-- title:
--   Hermitian Lattices Theory: class Set Assembly rat Cast mul
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly rat Cast mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L28-L32

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_ratCast_mul (q : ℚ) (a : K) :
    Algebra.trace ℚ K ((q : K) * a) = q * Algebra.trace ℚ K a := by sorry
