-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_discr
-- name    : Formalism.HermitianLatticesTheory.genusCovolBound_discr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:51.209794+00:00
-- url     : https://prove2.me/theorems/bee92c40-a3be-4380-a8f5-43d761a20c68
-- title:
--   Hermitian Lattices Theory: genus Covol Bound discr
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol Bound discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L198-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L198-L264

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

theorem Formalism.HermitianLatticesTheory.genusCovolBound_discr (a : K)
    (ha : ∀ r : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (a * algebraMap (𝓞 K) K r) = z) :
    ((NumberField.discr K : ℤ) : K) * a ∈ (1 : Submodule (𝓞 K) K) := by sorry
