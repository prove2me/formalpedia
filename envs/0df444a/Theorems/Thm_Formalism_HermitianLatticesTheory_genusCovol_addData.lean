-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_addData
-- name    : Formalism.HermitianLatticesTheory.genusCovol_addData
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:20.206625+00:00
-- url     : https://prove2.me/theorems/d728a28e-8d3f-48d2-b975-ab7857e66960
-- title:
--   Hermitian Lattices Theory: genus Covol add Data
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol add Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L554-L558
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L554-L558

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

theorem Formalism.HermitianLatticesTheory.genusCovol_addData (g : V ≃ₗ[K] V) (X Y : Submodule (𝓞 K) V) (hXY : gmap g X = Y) :
    X.toAddSubgroup.map (((g : V →ₗ[K] V).restrictScalars (𝓞 K) : V →ₗ[𝓞 K] V) : V →+ V) =
      Y.toAddSubgroup := by sorry
