-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetFinite_of
-- name    : Formalism.HermitianLatticesTheory.classSetFinite_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:52.973832+00:00
-- url     : https://prove2.me/theorems/3614df2f-f6d3-4b80-8b6e-f64c425d71a6
-- title:
--   Hermitian Lattices Theory: class Set Finite of
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Finite of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L746-L757
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetAssembly.lean#L746-L757

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

theorem Formalism.HermitianLatticesTheory.classSetFinite_of (hA : TraceReal) (hB : GenusCovolBound) (hC : ShortVectors)
    (hD : GenusScale) (hE : FinIntermediate) (hF : IsomOfTrace) : ClassSetFinite := by sorry
