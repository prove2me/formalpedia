-- Prove2me | Theorems.Thm_Formalism_HN_hnSum_split
-- name    : Formalism.HN.hnSum_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:27.719312+00:00
-- url     : https://prove2.me/theorems/7cca0238-abda-480a-808e-7ca3d995eebd
-- title:
--   HN: hn Sum split
-- statement:
--   The HN construction uses the hn Sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PolygonSlopeSum.lean#L116-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PolygonSlopeSum.lean#L116-L133

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
universe u v w x
variable {R : Type u} {V : Type v} {E : Type w} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)

theorem Formalism.HN.hnSum_split (h1 : DegSupermod.{u, v, w}) {A B : Submodule R V} (hA : IsLat ρ A)
    (hB : IsLat ρ B) (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) {N : Submodule R V}
    (hN : N ≤ A ⊔ B) :
    deg ρ N ≤ deg ρ (N ⊓ A) + deg ρ (B ⊓ (N ⊔ A)) ∧
      rk ρ N = rk ρ (N ⊓ A) + rk ρ (B ⊓ (N ⊔ A)) := by sorry
