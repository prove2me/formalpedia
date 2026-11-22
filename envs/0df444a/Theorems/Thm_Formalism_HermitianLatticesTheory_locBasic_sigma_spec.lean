-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_sigma_spec
-- name    : Formalism.HermitianLatticesTheory.locBasic_sigma_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:47.235861+00:00
-- url     : https://prove2.me/theorems/f6e50e68-ee0e-4284-8042-6867c4d11e34
-- title:
--   Hermitian Lattices Theory: loc Basic sigma spec
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Basic sigma spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L131-L133

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

theorem Formalism.HermitianLatticesTheory.locBasic_sigma_spec (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (r : R) :
    algebraMap R K (locBasic_sigma hinj hstar r) = star (algebraMap R K r) := by sorry
