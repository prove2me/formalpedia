-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_sigma_mem
-- name    : Formalism.HermitianLatticesTheory.locDual_sigma_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:38.506381+00:00
-- url     : https://prove2.me/theorems/cb355c04-5eb7-4e5e-aa02-252a5b42338e
-- title:
--   Hermitian Lattices Theory: loc Dual sigma mem
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Dual sigma mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L94-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocDual.lean#L94-L110

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
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
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.HermitianLatticesTheory.locDual_sigma_mem (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R)
    (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by sorry
