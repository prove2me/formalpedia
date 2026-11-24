-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_offdiag
-- name    : Formalism.HermitianLatticesTheory.unimodUnramUnique_offdiag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:36.309844+00:00
-- url     : https://prove2.me/theorems/a2511d17-b4fc-4ecf-b28d-66d1d0aa01bf
-- title:
--   Hermitian Lattices Theory: unimod Unram Unique offdiag
-- statement:
--   The Hermitian Lattices Theory construction uses the unimod Unram Unique offdiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L199-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/UnimodUnramUnique.lean#L199-L237

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

theorem Formalism.HermitianLatticesTheory.unimodUnramUnique_offdiag [IsLocalRing R₀] (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x)
    {θ : R} (hθ : IsUnit (θ - star θ)) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι R) (hA : Aᴴ = A) (hdet : IsUnit A.det) (hdiag : ∀ i, ¬ IsUnit (A i i)) :
    ∃ i j c, i ≠ j ∧ IsUnit (c * A i j + star (c * A i j)) := by sorry
