-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_partner
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z2.plane_partner
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:58:35.805116+00:00
-- url     : https://prove2.me/theorems/89221b9a-8b16-4b31-8447-0ead564a07d3
-- title:
--   Z2: plane partner
-- statement:
--   The Z2 construction uses the plane partner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L138-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L138-L176

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem Formalism.L2.SG.Pf.LatDictZ.Z2.plane_partner {S : Subring K} (hS : IsHermSemilocal S) (B : V →ₗ⋆[K] V →ₗ[K] K)
    (hsym : ∀ x y, star (B x y) = B y x) {N : AddSubgroup V} (hsm : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N)
    (hint : ∀ x ∈ N, ∀ y ∈ N, B x y ∈ S) (hdual : ∀ x, (∀ m ∈ N, B m x ∈ S) → x ∈ N) {v : V}
    (hv : v ∈ N) (hprim : ∀ c : K, c • v ∈ N → c ∈ S) {m0 : V} (hm0 : m0 ∈ N) (hne : B v m0 ≠ 0) :
    ∃ m ∈ N, B v m = 1 := by sorry
