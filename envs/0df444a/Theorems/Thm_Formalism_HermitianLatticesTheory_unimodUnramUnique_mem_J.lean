-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_mem_J
-- name    : Formalism.HermitianLatticesTheory.unimodUnramUnique_mem_J
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:37.711455+00:00
-- url     : https://prove2.me/theorems/71d744b6-114e-4d28-83b9-420e03632b2c
-- title:
--   Hermitian Lattices Theory: unimod Unram Unique mem J
-- statement:
--   The Hermitian Lattices Theory construction uses the unimod Unram Unique mem J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L192-L193

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

theorem Formalism.HermitianLatticesTheory.unimodUnramUnique_mem_J [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) (r : R) :
    r ∈ unimodUnramUnique_J hR₀ ↔ ∀ c : R, ¬ IsUnit (c * r + star (c * r)) := by sorry
