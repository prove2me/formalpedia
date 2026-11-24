-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_local
-- name    : Formalism.HermitianLatticesTheory.genusCovol_local
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:37.137709+00:00
-- url     : https://prove2.me/theorems/10976be0-4ac4-419e-b1c5-597d2edff67e
-- title:
--   Hermitian Lattices Theory: genus Covol local
-- statement:
--   The Hermitian Lattices Theory construction uses the genus Covol local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L532-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/GenusCovol.lean#L532-L552

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

theorem Formalism.HermitianLatticesTheory.genusCovol_local (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule (𝓞 K) V) (hLfg : L.FG)
    (hMfg : M.FG) (P : Ideal (𝓞 K)) [P.IsPrime] (g : V ≃ₗ[K] V) (hg : g ∈ isom h)
    (hgL : gmap g (loc (K := K) P L) = loc (K := K) P M) :
    gmap g (locS P.primeCompl L) = locS P.primeCompl M ∧
    gmap g (locS P.primeCompl (genusCovol_tdual h L)) =
      locS P.primeCompl (genusCovol_tdual h M) := by sorry
