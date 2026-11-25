-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_embK_conj
-- name    : Formalism.L2.FormalSeriesBounds.embK_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:07.082893+00:00
-- url     : https://prove2.me/theorems/0ceecd4b-d9f8-43e7-8b69-01892c217857
-- title:
--   Formal Series Bounds: emb K conj
-- statement:
--   The Formal Series Bounds construction uses the emb K conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieLab.lean#L98-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieLab.lean#L98-L105

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
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
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem Formalism.L2.FormalSeriesBounds.embK_conj (hstar : ∀ a : 𝓞 E, star a = H.bar a) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (star x) := by sorry
