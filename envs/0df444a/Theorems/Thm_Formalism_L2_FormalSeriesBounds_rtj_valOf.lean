-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_valOf
-- name    : Formalism.L2.FormalSeriesBounds.rtj_valOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:09.37113+00:00
-- url     : https://prove2.me/theorems/92cc7841-56b5-47c5-a28a-748a53fbe8d3
-- title:
--   Formal Series Bounds: rtj val Of
-- statement:
--   The Formal Series Bounds construction uses the rtj val Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L334-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L334-L340

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
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
open Formalism.IncomingBounds
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}

theorem Formalism.L2.FormalSeriesBounds.rtj_valOf (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) {M : ℕ}
    (P : MvPolynomial (Fin M × WV I) C) (kind : Fin M → Knd d) (gr : Fin M → MvPowerSeries (WV I) C) :
    ValOf hL P kind gr =
      jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ (rtjH hL (kind ρ))))) := by sorry
