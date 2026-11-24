-- Prove2me | Theorems.Thm_Formalism_ZRN_e_ofReal
-- name    : Formalism.ZRN.e_ofReal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:41:59.459846+00:00
-- url     : https://prove2.me/theorems/45ab90b1-2e14-4f8e-b253-8aebada63b9b
-- title:
--   ZRN: e of Real
-- statement:
--   The ZRN construction uses the e of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L264-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L264-L269

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN

theorem Formalism.ZRN.e_ofReal (n : ℕ) (σ : ℝ) : e n σ = (er n σ : ℂ) := by sorry
