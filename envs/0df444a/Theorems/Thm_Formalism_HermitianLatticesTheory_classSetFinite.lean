-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_classSetFinite
-- name    : Formalism.HermitianLatticesTheory.classSetFinite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:26.962257+00:00
-- url     : https://prove2.me/theorems/b11d5ec3-ec43-400b-bf35-67c94dafa3d1
-- title:
--   Hermitian Lattices Theory: class Set Finite
-- statement:
--   The Hermitian Lattices Theory construction uses the class Set Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetFinite.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ClassSetFinite.lean#L11-L12

import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ShortVectors
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomOfTrace
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticesTheory

theorem Formalism.HermitianLatticesTheory.classSetFinite : ClassSetFinite := by sorry
