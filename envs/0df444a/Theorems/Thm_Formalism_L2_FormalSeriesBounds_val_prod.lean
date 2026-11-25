-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_val_prod
-- name    : Formalism.L2.FormalSeriesBounds.val_prod
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:54.285732+00:00
-- url     : https://prove2.me/theorems/8890b245-b929-5e76-a1cf-22debf9c1574
-- title:
--   Formal Series Bounds: val prod
-- statement:
--   The Formal Series Bounds construction uses the val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieVal.lean#L106-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieVal.lean#L106-L117

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
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
attribute [instance] LetSys.fin
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable {d : ℕ} [NeZero d]
variable {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)

theorem Formalism.L2.FormalSeriesBounds.val_prod (hb : BddBelow (Y.valSet Ls n)) (hs : PairsSep Y p) (hv : ValEqPSt Y p H Ls n)
    (P : MvPolynomial (Ls.ι n) C) (hP : P ∈ Ls.FF n) (Po : ∀ o, MvPolynomial (Fin n × WV (I o)) C)
    (hQ : IsImgO (fun o => Y.raw (p o)) (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o)))
    (kind : Orb → Fin n → Option (Fin 2 × ZMod d × ZMod d))
    (hk : ∀ o, RowsOK ((Y.raw (p o)).rowData (H o)).G ((Y.raw (p o)).rowData (H o)).Alt (Po o) (kind o))
    (S : ∀ o g, Sys (((Y.raw (p o)).rowData (H o)).G g)) (t : ∀ o g, I o g → MvPowerSeries (I o g) C)
    (ht : ∀ o g, (S o g).IsT (t o g))
    (gr : ∀ o, Fin n → MvPowerSeries (WV (I o)) C) (hg : ∀ o ρ, gr o ρ ∈ IntGerm V (t o)) :
    Y.nuPl Ls n ≤ ∑ o, V.v (ValOf ((Y.raw (p o)).rowData (H o)).hL (Po o) (kind o) (gr o)) := by sorry
