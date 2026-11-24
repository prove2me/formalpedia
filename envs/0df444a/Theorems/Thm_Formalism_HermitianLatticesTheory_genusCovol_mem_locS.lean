-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_mem_locS
-- name    : Formalism.HermitianLatticesTheory.genusCovol_mem_locS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:21.920536+00:00
-- url     : https://prove2.me/theorems/145ca944-2c9b-44d0-8efd-b4a83d95dabc
-- title:
--   Hermitian Lattices Theory: genus Covol mem loc S
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol mem loc S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L20-L21

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

theorem Formalism.HermitianLatticesTheory.genusCovol_mem_locS (S : Submonoid R) (L : Submodule R W) (x : W) :
    x ∈ locS S L ↔ ∃ s ∈ S, s • x ∈ L := by sorry
