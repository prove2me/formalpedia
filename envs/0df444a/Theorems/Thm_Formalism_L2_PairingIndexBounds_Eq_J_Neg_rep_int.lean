-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_rep_int
-- name    : Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:24.210397+00:00
-- url     : https://prove2.me/theorems/a36d86fb-9f21-422b-9c4e-4ec476657748
-- title:
--   Neg: rep int
-- statement:
--   The Neg construction uses the rep int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L137-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L137-L149

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq.J.Neg

theorem Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_int (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (m : ℕ) (hm : 0 < m) :
    ∃ α β γ δ s : ℤ, (α ^ 2 + q * β ^ 2) * (γ ^ 2 + d * δ ^ 2) = -1 + m * s := by sorry
