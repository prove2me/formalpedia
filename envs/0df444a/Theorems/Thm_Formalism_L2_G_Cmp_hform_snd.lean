-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_hform_snd
-- name    : Formalism.L2.G.Cmp.hform_snd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:31.705702+00:00
-- url     : https://prove2.me/theorems/ce3c1080-713a-4f1f-b424-aa25a3bd041b
-- title:
--   Cmp: hform snd
-- statement:
--   The Cmp construction uses the hform snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsHypA.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsHypA.lean#L20-L22

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

theorem Formalism.L2.G.Cmp.hform_snd (z y : n → T) :
    (φ (hform σ J z y)).2 = ∑ i, ∑ j, (φ (z i)).1 * (φ (J i j)).2 * (φ (y j)).2 := by sorry
