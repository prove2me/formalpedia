-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_mem_zmap
-- name    : Formalism.HermitianLatticesTheory.genusCovolBound_mem_zmap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:20:05.474024+00:00
-- url     : https://prove2.me/theorems/7b9b88fb-5e9a-4e95-9bc0-9583cb98538b
-- title:
--   Hermitian Lattices Theory: genus Covol Bound mem zmap
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol Bound mem zmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovolBound.lean#L20-L23

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

theorem Formalism.HermitianLatticesTheory.genusCovolBound_mem_zmap (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N))
    (M : Submodule (𝓞 K) V) (v : EuclideanSpace ℝ (Fin N)) :
    v ∈ zmap ι M ↔ ∃ x ∈ M, ι x = v := by sorry
