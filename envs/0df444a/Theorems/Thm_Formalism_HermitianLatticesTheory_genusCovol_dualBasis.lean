-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_dualBasis
-- name    : Formalism.HermitianLatticesTheory.genusCovol_dualBasis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:25.149666+00:00
-- url     : https://prove2.me/theorems/c8353a4a-174d-4b3f-9ce5-02174928f5cf
-- title:
--   Hermitian Lattices Theory: genus Covol dual Basis
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol dual Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L309-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L309-L443

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

theorem Formalism.HermitianLatticesTheory.genusCovol_dualBasis (h : V →ₗ⋆[K] V →ₗ[K] K) (N : ℕ)
    (ι : V →+ EuclideanSpace ℝ (Fin N))
    (hι : ∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ))
    (M : Submodule (𝓞 K) V) [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)] :
    ∃ bv : Basis (Module.Free.ChooseBasisIndex ℤ (zmap ι M)) ℝ (EuclideanSpace ℝ (Fin N)),
      zmap ι (genusCovol_tdual h M) = Submodule.span ℤ (Set.range bv) ∧
      ZLattice.covolume (zmap ι M) * ZLattice.covolume (Submodule.span ℤ (Set.range bv)) = 1 := by sorry
