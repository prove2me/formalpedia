-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_sup
-- name    : Formalism.HermitianLatticesTheory.locBasic_locS_sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:25.319987+00:00
-- url     : https://prove2.me/theorems/6f0e1c6f-8b7d-42e4-b55c-6b19bd5d2e9e
-- title:
--   Hermitian Lattices Theory: loc Basic loc S sup
-- statement:
--   The Hermitian Lattices Theory construction uses the loc Basic loc S sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/LocBasic.lean#L76-L92

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
variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.HermitianLatticesTheory.locBasic_locS_sup (S : Submonoid R) (hS : ∀ s ∈ S, algebraMap R K s ≠ 0)
    (L M : Submodule R V) : locS S (L ⊔ M) = locS S L ⊔ locS S M := by sorry
