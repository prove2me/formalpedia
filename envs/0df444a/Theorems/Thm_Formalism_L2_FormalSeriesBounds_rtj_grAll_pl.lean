-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_grAll_pl
-- name    : Formalism.L2.FormalSeriesBounds.rtj_grAll_pl
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:11.634802+00:00
-- url     : https://prove2.me/theorems/061f0730-a9c3-44b5-9c22-8a165e41f5e2
-- title:
--   Formal Series Bounds: rtj gr All pl
-- statement:
--   The Formal Series Bounds construction uses the rtj gr All pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L361-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L361-L368

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

theorem Formalism.L2.FormalSeriesBounds.rtj_grAll_pl {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (gr : ∀ i, Fin (what₂ i) → MvPowerSeries (WV I) C) (s : Σ i : Fin K, Fin (what₂ i)) :
    grAll pl gr (pl s) = gr s.1 s.2 := by sorry
