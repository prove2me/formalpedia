-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_diag
-- name    : Formalism.HermitianLatticesTheory.unimodUnramUnique_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:25.399965+00:00
-- url     : https://prove2.me/theorems/f9bd0a82-b5b9-4552-a550-56c727395b55
-- title:
--   Hermitian Lattices Theory: unimod Unram Unique diag
-- statement:
--   The Hermitian Lattices Theory construction uses the unimod Unram Unique diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L298-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L298-L343

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

theorem Formalism.HermitianLatticesTheory.unimodUnramUnique_diag [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι R) (hA : Aᴴ = A)
    (hdet : IsUnit A.det) : ∃ g : Matrix ι ι R, IsUnit g.det ∧ ∃ i, (gᴴ * A * g) i i = 1 := by sorry
