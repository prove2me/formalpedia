-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_first_family_subset_image
-- name    : Formalism.L2.FormalSeriesBounds.RF.first_family_subset_image
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:43.257509+00:00
-- url     : https://prove2.me/theorems/b5668a47-ead6-5777-a849-a48afa05387b
-- title:
--   RF: first family subset image
-- statement:
--   The RF construction uses the first family subset image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjCharts.lean#L112-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjCharts.lean#L112-L121

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
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

theorem Formalism.L2.FormalSeriesBounds.RF.first_family_subset_image {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ}
    (plc : Fin N × Fin 2 ↪ Fin n) :
    selfConjTuplesInLattice Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc ⊆
      imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc := by sorry
