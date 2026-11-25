-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_nuLocC_le_nval
-- name    : Formalism.L2.FormalSeriesBounds.nuLocC_le_nval
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:39.302281+00:00
-- url     : https://prove2.me/theorems/f5c6d205-d86a-4265-9868-c0c89a104904
-- title:
--   Formal Series Bounds: nu Loc C le nval
-- statement:
--   The Formal Series Bounds construction uses the nu Loc C le nval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieDesc.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieDesc.lean#L25-L29

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
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
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem Formalism.L2.FormalSeriesBounds.nuLocC_le_nval (C3 : IntChart T io y) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (P : MvPolynomial (LtN Dw n) T.Fr) (hP : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n (chD C3.ch)) (hf : IsIntPS T f) :
    nuLocC C3 e k a n ≤ nval T.V e (chartDerivativeCoefficient C3 k n f P) := by sorry
