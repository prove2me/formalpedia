-- Prove2me | Theorems.Thm_Formalism_ZRN_e_crude
-- name    : Formalism.ZRN.e_crude
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:42:07.42221+00:00
-- url     : https://prove2.me/theorems/9b986a02-e0ad-4448-b51a-7b68a2a84dc7
-- title:
--   ZRN: e crude
-- statement:
--   The ZRN construction uses the e crude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L99-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaRealNonvanish.lean#L99-L126

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

theorem Formalism.ZRN.e_crude (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖e n s‖ ≤ ‖1 - s‖ + 2 * ((n : ℝ) + 1) + 1 := by sorry
