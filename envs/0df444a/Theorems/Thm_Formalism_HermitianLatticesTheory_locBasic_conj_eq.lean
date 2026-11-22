-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_conj_eq
-- name    : Formalism.HermitianLatticesTheory.locBasic_conj_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:02:23.099409+00:00
-- url     : https://prove2.me/theorems/418e2b54-012d-4721-923e-6759e03ff603
-- title:
--   Hermitian Lattices Theory: loc Basic conj eq
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Basic conj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L135-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L135-L151

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

theorem Formalism.HermitianLatticesTheory.locBasic_conj_eq (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R) :
    conjIdeal (K := K) p = p.comap (locBasic_sigma hinj hstar) := by sorry
