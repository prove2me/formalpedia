-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le_conj
-- name    : Formalism.HermitianLatticesTheory.locBasic_hcompl_le_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:25.140631+00:00
-- url     : https://prove2.me/theorems/a98ebc33-7ae6-4a82-8852-5d4a703de6e9
-- title:
--   Hermitian Lattices Theory: loc Basic hcompl le conj
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Basic hcompl le conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L153-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L153-L161

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

theorem Formalism.HermitianLatticesTheory.locBasic_hcompl_le_conj (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R)
    [(conjIdeal (K := K) p).IsPrime] :
    hcompl (K := K) p ≤ (conjIdeal (K := K) p).primeCompl := by sorry
