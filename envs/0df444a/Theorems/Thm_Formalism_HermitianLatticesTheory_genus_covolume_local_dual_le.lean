-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genus_covolume_local_dual_le
-- name    : Formalism.HermitianLatticesTheory.genus_covolume_local_dual_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:33.397122+00:00
-- url     : https://prove2.me/theorems/3bfcff00-8c5d-41a9-944b-b1fdbe745d6d
-- title:
--   Hermitian Lattices Theory: genus covolume local dual le
-- statement:
--   The Hermitian Lattices Theory construction uses the genus covolume local dual le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L264-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L264-L300

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

theorem Formalism.HermitianLatticesTheory.genus_covolume_local_dual_le (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V) (hg : g ∈ isom h)
    (P : Ideal (𝓞 K)) [P.IsPrime] (L M : Submodule (𝓞 K) V) (hM : M.FG)
    (hML : M ≤ gmap g (loc (K := K) P L)) :
    gmap g (locS P.primeCompl (genusCovol_tdual h L)) ≤
      locS P.primeCompl (genusCovol_tdual h M) := by sorry
