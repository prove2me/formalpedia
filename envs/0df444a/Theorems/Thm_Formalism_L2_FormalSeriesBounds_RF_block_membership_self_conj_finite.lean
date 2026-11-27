-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_block_membership_self_conj_finite
-- name    : Formalism.L2.FormalSeriesBounds.RF.block_membership_self_conj_finite
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-27T05:51:25.842254+00:00
-- url     : https://prove2.me/theorems/58092387-3bde-5a4a-949a-f755b522f75a
-- title:
--   RF: block membership self conj finite
-- statement:
--   The RF construction uses the block membership self conj finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCFin.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCFin.lean#L20-L29

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCHarm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCFin
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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

theorem Formalism.L2.FormalSeriesBounds.RF.block_membership_self_conj_finite {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
    (F : ∀ o, Flag (rdS Y (selfOfLab ha hg) Hy o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (std : ∀ o g t (q : Fin ((rdS Y (selfOfLab ha hg) Hy o).rkF g t)), ((F o).en g t q).2.val = q.val)
    (alt : ∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt) (hj : lab.j' < lab.n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s)
    (tie : WtTieC Dw.mult lab.tau gaC fun τ i => a (τ, i)) :
    BlockMembershipSelfConjugate (fun o => rdS Y (selfOfLab ha hg) Hy o) N F (imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc) gaC := by sorry
