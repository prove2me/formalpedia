-- Prove2me | Theorems.Thm_Formalism_HN_range_comp_eq_imageLattice
-- name    : Formalism.HN.range_comp_eq_imageLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:33.095278+00:00
-- url     : https://prove2.me/theorems/18e381f2-0fa2-447e-9c95-2ee82371a9c2
-- title:
--   HN: range comp eq image Lattice
-- statement:
--   The HN construction uses the range comp eq image Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L206-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L206-L216

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem Formalism.HN.range_comp_eq_imageLattice {R V E G : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [AddCommGroup G] (ρ : V →+ E)
    (N : Submodule R V) (j : G →+ V) (hj : ∀ v, v ∈ N ↔ ∃ g, j g = v) :
    LinearMap.range (ρ.comp j).toIntLinearMap = zl ρ N := by sorry
