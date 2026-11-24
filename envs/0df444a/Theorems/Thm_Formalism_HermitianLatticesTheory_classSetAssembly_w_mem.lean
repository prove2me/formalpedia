-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_w_mem
-- name    : Formalism.HermitianLatticesTheory.classSetAssembly_w_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:24.017932+00:00
-- url     : https://prove2.me/theorems/7eba8fff-6265-4c6c-aa35-731d25b45ff8
-- title:
--   Hermitian Lattices Theory: class Set Assembly w mem
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Assembly w mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L550-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L550-L556

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

theorem Formalism.HermitianLatticesTheory.classSetAssembly_w_mem (o : Option (Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K))) :
    ∃ r : NumberField.RingOfIntegers K,
      o.elim (1 : K) (NumberField.integralBasis K) = algebraMap _ K r := by sorry
