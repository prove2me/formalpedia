-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_norm
-- name    : Formalism.HermitianLatticesTheory.unimodUnramUnique_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:27.49637+00:00
-- url     : https://prove2.me/theorems/4f99da1c-9291-4f0c-8155-a8abb4cb1bba
-- title:
--   Hermitian Lattices Theory: unimod Unram Unique norm
-- statement:
--   The Hermitian Lattices Theory construction uses the unimod Unram Unique norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L239-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L239-L266

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
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
open Polynomial IsLocalRing Matrix
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}

theorem Formalism.HermitianLatticesTheory.unimodUnramUnique_norm [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ)) {d : R}
    (hd : star d = d) (hdu : IsUnit d) : ∃ w : R, star w * w = d := by sorry
