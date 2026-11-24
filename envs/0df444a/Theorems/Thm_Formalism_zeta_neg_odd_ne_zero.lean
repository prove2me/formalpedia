-- Prove2me | Theorems.Thm_Formalism_zeta_neg_odd_ne_zero
-- name    : Formalism.zeta_neg_odd_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:26.798802+00:00
-- url     : https://prove2.me/theorems/11d3958d-2fcd-4347-baef-c365dff7e717
-- title:
--   Formalism: zeta neg odd ne zero
-- statement:
--   The Formalism construction uses the zeta neg odd ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RHofHalfPlane.lean#L9-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RHofHalfPlane.lean#L9-L42

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_RHofHalfPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism

theorem Formalism.zeta_neg_odd_ne_zero (m : ℕ) : riemannZeta (-((2 * m + 1 : ℕ) : ℂ)) ≠ 0 := by sorry
