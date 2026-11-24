-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_hform_fst
-- name    : Formalism.L2.G.Cmp.hform_fst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:14.329342+00:00
-- url     : https://prove2.me/theorems/00600738-434c-4326-a3ad-c853602fd04d
-- title:
--   Cmp: hform fst
-- statement:
--   The Cmp construction uses the hform fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsHypA.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsHypA.lean#L15-L17

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsHypA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
variable {T K : Type} [CommRing T] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
  (φ : T ≃+* K × K) (σ : T →+* T) (hσ : ∀ t, φ (σ t) = swapR K (φ t)) (Ov : Subring K) (S : Subring T)
  (hS : ∀ t, t ∈ S ↔ (φ t).1 ∈ Ov ∧ (φ t).2 ∈ Ov) (J : Matrix n n T) (Λ : Submodule S (n → T))
  (hΛ : ∀ y, y ∈ Λ ↔ ∀ z ∈ Λ, hform σ J z y ∈ S)
include hσ

theorem Formalism.L2.G.Cmp.hform_fst (z y : n → T) :
    (φ (hform σ J z y)).1 = ∑ i, ∑ j, (φ (z i)).2 * (φ (J i j)).1 * (φ (y j)).1 := by sorry
