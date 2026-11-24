-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_dual_genus
-- name    : Formalism.HermitianLatticesTheory.genusCovolBound_dual_genus
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:23.782796+00:00
-- url     : https://prove2.me/theorems/b62a5552-9d03-499f-bdee-f49aaa669c48
-- title:
--   Hermitian Lattices Theory: genus Covol Bound dual genus
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol Bound dual genus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L179-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L179-L196

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

theorem Formalism.HermitianLatticesTheory.genusCovolBound_dual_genus [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K))
    (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (M : Submodule (𝓞 K) V)
    (hM : M ∈ genus h L) : dual h M ∈ genus h (dual h L) := by sorry
