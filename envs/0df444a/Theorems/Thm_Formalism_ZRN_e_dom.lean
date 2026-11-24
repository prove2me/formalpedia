-- Prove2me | Theorems.Thm_Formalism_ZRN_e_dom
-- name    : Formalism.ZRN.e_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:29.314808+00:00
-- url     : https://prove2.me/theorems/ef031d6c-489e-488c-a54e-c5ad13a28b2a
-- title:
--   ZRN: e dom
-- statement:
--   The ZRN construction uses the e dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L135-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L135-L182

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

theorem Formalism.ZRN.e_dom (s₀ : ℂ) (h : 0 < s₀.re) : ∃ r > 0, ∃ u : ℕ → ℝ, Summable u ∧
    ∀ n : ℕ, ∀ w ∈ Metric.ball s₀ r, ‖e n w‖ ≤ u n := by sorry
