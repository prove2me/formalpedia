-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_hcompl
-- name    : Formalism.HermitianLatticesTheory.locBasic_mem_hcompl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:25.33375+00:00
-- url     : https://prove2.me/theorems/7d0666fa-697b-4195-a69a-db10421bfcdd
-- title:
--   Hermitian Lattices Theory: loc Basic mem hcompl
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Basic mem hcompl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L110-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L110-L117

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
variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]

theorem Formalism.HermitianLatticesTheory.locBasic_mem_hcompl (p : Ideal R) (u : R) (hu : u ∉ p) (hu' : u ∉ conjIdeal (K := K) p) :
    u ∈ hcompl (K := K) p := by sorry
