-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_int_conj_iff
-- name    : Formalism.L2.G.Cmp.int_conj_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:37.278526+00:00
-- url     : https://prove2.me/theorems/a647a8e6-a70e-4343-ba89-4bd9ba118080
-- title:
--   Cmp: int conj iff
-- statement:
--   The Cmp construction uses the int conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsHypA.lean#L84-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsHypA.lean#L84-L109

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

theorem Formalism.L2.G.Cmp.int_conj_iff {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n] (Ov : Subring K) (fr g : GL n K) :
    (∀ t : n → K, (∀ a, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ t) a ∈ Ov) →
      ∀ a, (((fr⁻¹ : GL n K) : Matrix n n K) *ᵥ ((g : Matrix n n K) *ᵥ t)) a ∈ Ov) ↔
      ∀ a b, ((fr⁻¹ * g * fr : GL n K) : Matrix n n K) a b ∈ Ov := by sorry
