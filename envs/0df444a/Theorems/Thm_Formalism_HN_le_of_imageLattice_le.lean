-- Prove2me | Theorems.Thm_Formalism_HN_le_of_imageLattice_le
-- name    : Formalism.HN.le_of_imageLattice_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:20.289424+00:00
-- url     : https://prove2.me/theorems/267e8ca1-e796-480f-a288-8905d0a26438
-- title:
--   HN: le of image Lattice le
-- statement:
--   The HN construction uses the le of image Lattice le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/RatioMax.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/RatioMax.lean#L12-L22

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.le_of_imageLattice_le {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) (L N₁ N₂ : Submodule R V)
    (hinj : Set.InjOn ρ (L : Set V)) (h₁ : N₁ ≤ L) (h₂ : N₂ ≤ L) (h : zl ρ N₁ ≤ zl ρ N₂) :
    N₁ ≤ N₂ := by sorry
