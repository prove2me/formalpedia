-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono
-- name    : Formalism.HermitianLatticesTheory.locBasic_locS_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:37.636513+00:00
-- url     : https://prove2.me/theorems/e3cdef42-acd6-47d2-8cfb-b297cddf73d3
-- title:
--   Hermitian Lattices Theory: loc Basic loc S mono
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Basic loc S mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L19-L23

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

theorem Formalism.HermitianLatticesTheory.locBasic_locS_mono (S : Submonoid R) {L M : Submodule R W} (h : L ≤ M) :
    locS S L ≤ locS S M := by sorry
