-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_covol_le
-- name    : Formalism.HermitianLatticesTheory.genusCovolBound_covol_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:51.972537+00:00
-- url     : https://prove2.me/theorems/93a2a9f6-0064-44d4-aa00-de3a319f7763
-- title:
--   Hermitian Lattices Theory: genus Covol Bound covol le
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol Bound covol le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L25-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L25-L152

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLatticesTheory.genusCovolBound_covol_le (h : V →ₗ⋆[K] V →ₗ[K] K) (N : ℕ)
    (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)]
    (D : ℕ) (hD0 : 0 < D)
    (hD : ∀ y y' : V, (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z) →
       (∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y') = z) →
       ∃ z : ℤ, (D : ℚ) * Algebra.trace ℚ K (h y y') = z) :
    ZLattice.covolume (zmap ι M) ≤ Real.sqrt ((D : ℝ) ^ N) := by sorry
