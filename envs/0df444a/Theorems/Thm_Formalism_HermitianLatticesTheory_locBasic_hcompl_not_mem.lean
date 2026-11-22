-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_not_mem
-- name    : Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:48.073357+00:00
-- url     : https://prove2.me/theorems/c80ae5b6-2c4a-4aa8-a3c8-32e110b1ccda
-- title:
--   Hermitian Lattices Theory: loc Basic hcompl not mem
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Basic hcompl not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L107-L108

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

theorem Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (p : Ideal R) [p.IsPrime] (s : R) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p := by sorry
