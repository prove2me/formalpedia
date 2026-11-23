-- Prove2me | Theorems.Thm_Formalism_ZRN_norm_cpow_nat
-- name    : Formalism.ZRN.norm_cpow_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:29.357273+00:00
-- url     : https://prove2.me/theorems/ce64a4a6-05b3-4170-8381-22369d9e7fde
-- title:
--   ZRN: norm cpow nat
-- statement:
--   The ZRN construction uses the norm cpow nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L94-L97

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

theorem Formalism.ZRN.norm_cpow_nat (n : ℕ) (k : ℝ) (hk : 0 < (n : ℝ) + k) (w : ℂ) :
    ‖((n : ℂ) + (k : ℂ)) ^ w‖ = ((n : ℝ) + k) ^ w.re := by sorry
