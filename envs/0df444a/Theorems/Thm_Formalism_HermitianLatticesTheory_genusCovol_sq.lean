-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_sq
-- name    : Formalism.HermitianLatticesTheory.genusCovol_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:25.376811+00:00
-- url     : https://prove2.me/theorems/2e05dca1-0bde-4f36-806e-1a89880570e5
-- title:
--   Hermitian Lattices Theory: genus Covol sq
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L459-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L459-L523

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
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

theorem Formalism.HermitianLatticesTheory.genusCovol_sq (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (N : ℕ)
    (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (A : Submodule (𝓞 K) V) [DiscreteTopology (zmap ι A)] [IsZLattice ℝ (zmap ι A)]
    (D : ℕ) (hD0 : 0 < D) (hD : ∀ x ∈ A, D • x ∈ genusCovol_tdual h A) :
    (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex A.toAddSubgroup ≠ 0 ∧
    (A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex (genusCovol_tdual h A).toAddSubgroup ≠ 0 ∧
    ZLattice.covolume (zmap ι A) ^ 2 *
        ((A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
      ((A ⊓ genusCovol_tdual h A).toAddSubgroup.relIndex (genusCovol_tdual h A).toAddSubgroup : ℝ) := by sorry
