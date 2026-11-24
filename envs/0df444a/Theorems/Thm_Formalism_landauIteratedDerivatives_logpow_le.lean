-- Prove2me | Theorems.Thm_Formalism_landauIteratedDerivatives_logpow_le
-- name    : Formalism.landauIteratedDerivatives.logpow_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:15.524091+00:00
-- url     : https://prove2.me/theorems/ef071d3a-2eb8-4274-89cc-d2b0f8556899
-- title:
--   landau Iterated Derivatives: logpow le
-- statement:
--   The landau Iterated Derivatives construction uses the logpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L29-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/LandauLemma.lean#L29-L48

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open Formalism.landauIteratedDerivatives

theorem Formalism.landauIteratedDerivatives.logpow_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ n ≤ (((n : ℝ) + 1) / ε) ^ n * x ^ ε := by sorry
