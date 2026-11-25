-- Prove2me | Theorems.Thm_Formalism_HN_hnSum_orth
-- name    : Formalism.HN.hnSum_orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:22.970084+00:00
-- url     : https://prove2.me/theorems/127ff432-5253-4cae-b93a-fa836127f018
-- title:
--   HN: hn Sum orth
-- statement:
--   The HN construction uses the hn Sum orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PolygonSlopeSum.lean#L56-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PolygonSlopeSum.lean#L56-L89

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
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
variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)
variable [FiniteDimensional ℝ E]

theorem Formalism.HN.hnSum_orth {A B : Submodule R V} (hA : IsLat ρ A) (hB : IsLat ρ B)
    (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) :
    IsLat ρ (A ⊔ B) ∧ A ⊓ B = ⊥ ∧ deg ρ (A ⊔ B) = deg ρ A + deg ρ B := by sorry
