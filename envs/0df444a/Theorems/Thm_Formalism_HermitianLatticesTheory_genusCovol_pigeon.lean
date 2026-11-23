-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_pigeon
-- name    : Formalism.HermitianLatticesTheory.genusCovol_pigeon
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:26.393941+00:00
-- url     : https://prove2.me/theorems/0a722b0b-64ce-4809-acf9-dceb16d49dc5
-- title:
--   Hermitian Lattices Theory: genus Covol pigeon
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol pigeon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L46-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L46-L69

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

theorem Formalism.HermitianLatticesTheory.genusCovol_pigeon {X Y : Submodule R W}
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) (r : R) {z : W} (hz : z ∈ Y) :
    ∃ m k : ℕ, 0 < k ∧ r ^ m • z - r ^ (m + k) • z ∈ X := by sorry
