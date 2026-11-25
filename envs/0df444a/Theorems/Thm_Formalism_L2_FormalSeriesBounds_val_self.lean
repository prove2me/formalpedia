-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_val_self
-- name    : Formalism.L2.FormalSeriesBounds.val_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:14:49.080811+00:00
-- url     : https://prove2.me/theorems/6abb04cb-0227-4ae9-894f-4c728f4a2720
-- title:
--   Formal Series Bounds: val self
-- statement:
--   The Formal Series Bounds construction uses the val self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieSelf.lean#L117-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieSelf.lean#L117-L134

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

theorem Formalism.L2.FormalSeriesBounds.val_self (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n) (N : ℕ) (pl : Fin N × Fin 2 ↪ Fin n)
    (P : MvPolynomial (Ls.ι n) C) (hP : P ∈ Ls.FF n) (Po : ∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C)
    (hQ : IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o)))
    (kind : Orb → Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (hk : ∀ o, RowsOK ((Y.rawSelf (p o)).rowData (H o)).G ((Y.rawSelf (p o)).rowData (H o)).Alt (Po o) (kind o))
    (S : ∀ o g, Sys (((Y.rawSelf (p o)).rowData (H o)).G g)) (t : ∀ o (_ : Fin 2), I0 o → MvPowerSeries (I0 o) C)
    (ht : ∀ o g, (S o g).IsT (t o g))
    (gr : ∀ o, Fin N → MvPowerSeries (WV fun _ => I0 o) C) (hg : ∀ o ρ, gr o ρ ∈ IntGerm V (t o)) :
    Y.nuPlE Ls n ≤ (WithBot.some
      (∑ o, V.v (ValOf ((Y.rawSelf (p o)).rowData (H o)).hL (Po o) (kind o) (gr o))) : WithBot (WithTop ℝ)) := by sorry
