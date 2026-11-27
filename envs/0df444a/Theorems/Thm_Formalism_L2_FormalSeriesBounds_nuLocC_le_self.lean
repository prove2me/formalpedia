-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_nuLocC_le_self
-- name    : Formalism.L2.FormalSeriesBounds.nuLocC_le_self
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:04:42.068398+00:00
-- url     : https://prove2.me/theorems/29fc9c44-8b8d-52f3-bc6f-7b77f55b7078
-- title:
--   Formal Series Bounds: nu Loc C le self
-- statement:
--   The Formal Series Bounds construction uses the nu Loc C le self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/SelfConjugateRowData.lean#L199-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/SelfConjugateRowData.lean#L199-L219

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

theorem Formalism.L2.FormalSeriesBounds.nuLocC_le_self [Fintype Orb] (hD : DescentSt Xo c) {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hv : ValEqSelfSt Y (selfOfLab ha hg) Hy (chartLetterSystem C3 V ι a) n)
    (N : ℕ) (pl : Fin N × Fin 2 ↪ Fin n)
    (P : MvPolynomial (LtN Dw n) C) (hP : P ∈ (chartLetterSystem C3 V ι a).FF n)
    (Po : ∀ o, MvPolynomial (Fin N × WV fun _ => lab.II Dw o) C)
    (hQ : IsImgS (fun o => Y.rawSelf (selfOfLab ha hg o)) pl ((chartLetterSystem C3 V ι a).cp n) ((chartLetterSystem C3 V ι a).uv n) P
      (∏ o, toAll o (Po o)))
    (kind : Orb → Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (hk : ∀ o, RowsOK ((Y.rawSelf (selfOfLab ha hg o)).rowData (Hy o)).G
      ((Y.rawSelf (selfOfLab ha hg o)).rowData (Hy o)).Alt (Po o) (kind o))
    (S : ∀ o g, Sys (((Y.rawSelf (selfOfLab ha hg o)).rowData (Hy o)).G g))
    (t : ∀ o (_ : Fin 2), lab.II Dw o → MvPowerSeries (lab.II Dw o) C) (ht : ∀ o g, (S o g).IsT (t o g))
    (gr : ∀ o, Fin N → MvPowerSeries (WV fun _ => lab.II Dw o) C) (hgr : ∀ o ρ, gr o ρ ∈ IntGerm V (t o)) :
    nuLocC C3 (eOf T V) k a n ≤
      (WithBot.some (∑ o, V.v (ValOf ((Y.rawSelf (selfOfLab ha hg o)).rowData (Hy o)).hL (Po o) (kind o) (gr o))) :
        WithBot (WithTop ℝ)) := by sorry
