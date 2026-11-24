-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_gmap_gmap_inv
-- name    : Formalism.HermitianLatticesTheory.genusCovol_gmap_gmap_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:23.284496+00:00
-- url     : https://prove2.me/theorems/f819f426-b055-45c6-bbeb-dee80da44d64
-- title:
--   Hermitian Lattices Theory: genus Covol gmap gmap inv
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol gmap gmap inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L259-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L259-L262

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

theorem Formalism.HermitianLatticesTheory.genusCovol_gmap_gmap_inv (g : V ≃ₗ[K] V) (Z : Submodule (𝓞 K) V) :
    gmap g (gmap g⁻¹ Z) = Z := by sorry
