-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hco_of_img
-- name    : Formalism.L2.FormalSeriesBounds.VP.hco_of_img
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:19.552605+00:00
-- url     : https://prove2.me/theorems/32c7f153-5347-519e-bf74-f4d7e5bd6560
-- title:
--   VP: hco of img
-- statement:
--   The VP construction uses the hco of img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GermLiftSelfSt.lean#L163-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GermLiftSelfSt.lean#L163-L191

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
open Formalism.L2.FormalSeriesBounds.VP
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)

theorem Formalism.L2.FormalSeriesBounds.VP.hco_of_img {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (ℓ : ι)
    (co : Fin N × WVO (IS I0) → C)
    (h : ∃ ρ col, pl (ρ, col) = cp ℓ ∧ (∀ ρ' w, ρ' ≠ ρ → co (ρ', w) = 0) ∧
      (fun x : Fin 2 × Fin dd => if x.1 = col then uv ℓ x.2 else 0) =
        ∑ w : WVO (IS I0), co (ρ, w) • (Y.rawSelf (p w.1)).u w.2.1 w.2.2) (b : Fin n) (i : Fin dd) :
    ∑ x, co x * MS Y p pl x (b, i) = if b = cp ℓ then uv ℓ i else 0 := by sorry
