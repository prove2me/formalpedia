-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_block_membership_self_conj_charts
-- name    : Formalism.L2.FormalSeriesBounds.RF.block_membership_self_conj_charts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:16:23.724092+00:00
-- url     : https://prove2.me/theorems/8ac5c059-97e1-52af-934a-68370d34a0b7
-- title:
--   RF: block membership self conj charts
-- statement:
--   The RF construction uses the block membership self conj charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjCharts.lean#L123-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjCharts.lean#L123-L139

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3

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
open Formalism.IncomingBounds Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

theorem Formalism.L2.FormalSeriesBounds.RF.block_membership_self_conj_charts (h1 : IsotropicToStdSubstHarmonic) (h2 : IsotropicToStdSubstLineInvariant) (h3 : IsotropicToStdSubstLineDegree)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
    (F : ∀ o, Flag (rdS Y (selfOfLab ha hg) Hy o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (std : ∀ o g t (q : Fin ((rdS Y (selfOfLab ha hg) Hy o).rkF g t)), ((F o).en g t q).2.val = q.val)
    (alt : ∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt) (hj : lab.j' < lab.n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s)
    (tie : WtTieC Dw.mult lab.tau gaC fun τ i => a (τ, i)) :
    BlockMembershipSelfConjugate (fun o => rdS Y (selfOfLab ha hg) Hy o) N F (imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc) gaC := by sorry
