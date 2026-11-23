-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_le_of_le
-- name    : Formalism.HermitianLatticesTheory.locBasic_locS_le_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:14.706744+00:00
-- url     : https://prove2.me/theorems/acec52f2-edaa-46fc-bfc2-22293f0b2ec9
-- title:
--   Hermitian Lattices Theory: loc Basic loc S le of le
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Basic loc S le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L25-L29

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem Formalism.HermitianLatticesTheory.locBasic_locS_le_of_le {S T : Submonoid R} (hST : S ≤ T) (L : Submodule R W) :
    locS S L ≤ locS T L := by sorry
