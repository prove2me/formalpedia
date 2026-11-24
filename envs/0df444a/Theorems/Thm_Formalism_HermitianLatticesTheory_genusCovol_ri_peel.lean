-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_ri_peel
-- name    : Formalism.HermitianLatticesTheory.genusCovol_ri_peel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:44.270798+00:00
-- url     : https://prove2.me/theorems/629de1fd-8b5f-424e-b6c5-31e855770b4d
-- title:
--   Hermitian Lattices Theory: genus Covol ri peel
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol ri peel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L117-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L117-L126

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem Formalism.HermitianLatticesTheory.genusCovol_ri_peel (S : Submonoid R) {X Y : Submodule R W} (hXY : X ≤ Y)
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) :
    (Y ⊓ locS S X).toAddSubgroup.relIndex Y.toAddSubgroup =
      (locS S X).toAddSubgroup.relIndex (locS S Y).toAddSubgroup := by sorry
