-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_prim_e
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.prim_e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:46:37.388871+00:00
-- url     : https://prove2.me/theorems/fcf7d0f5-5cad-4d59-b15d-189940d25d3a
-- title:
--   Pl: prim e
-- statement:
--   The Pl construction uses the prim e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieUpFBrPlP.lean#L64-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieUpFBrPlP.lean#L64-L84

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.prim_e [Module.Free ℤ OE] [Module.Finite ℤ OE] (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {ε : OE}
    (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    (hε3 : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y)
    {e z : ℤ_[l] ⊗[ℤ] OE} (hee : e * e = e) (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z)
    (f : ℤ_[l] ⊗[ℤ] OE) (hf : f * f = f) (hfe : f * e = f) : f = 0 ∨ f = e := by sorry
