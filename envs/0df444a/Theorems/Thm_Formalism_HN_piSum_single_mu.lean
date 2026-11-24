-- Prove2me | Theorems.Thm_Formalism_HN_piSum_single_mu
-- name    : Formalism.HN.piSum_single_mu
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:21.969797+00:00
-- url     : https://prove2.me/theorems/e17216db-8574-4466-8d41-78eec554c525
-- title:
--   HN: pi Sum single mu
-- statement:
--   The HN construction uses the pi Sum single mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PiSumForallInsertOnly.lean#L152-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PiSumForallInsertOnly.lean#L152-L190

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
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
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable (ρ : ∀ i, V i →+ E i)
variable [∀ i, FiniteDimensional ℝ (E i)]

theorem Formalism.HN.piSum_single_mu (L : ∀ i, Submodule R (V i)) (i : ι) (hL : IsLat (ρ i) (L i))
    (hL0 : L i ≠ ⊥) :
    piSumS L i ≠ ⊥ ∧ ∀ θ : ℝ,
      (muMax (piReal ρ) (piSumS L i) ≤ θ ↔ muMax (ρ i) (L i) ≤ θ) ∧
      (θ ≤ muMin (piReal ρ) (piSumS L i) ↔ θ ≤ muMin (ρ i) (L i)) := by sorry
