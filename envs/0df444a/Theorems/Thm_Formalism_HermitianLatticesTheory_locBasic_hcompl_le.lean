-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le
-- name    : Formalism.HermitianLatticesTheory.locBasic_hcompl_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:17:07.930055+00:00
-- url     : https://prove2.me/theorems/a9460713-ee6f-481b-8806-c7e1f8f6918b
-- title:
--   Hermitian Lattices Theory: loc Basic hcompl le
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Basic hcompl le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L100-L105

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

theorem Formalism.HermitianLatticesTheory.locBasic_hcompl_le (p : Ideal R) [p.IsPrime] :
    hcompl (K := K) p ≤ p.primeCompl := by sorry
