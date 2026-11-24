-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_rep_all
-- name    : Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_all
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:57.166835+00:00
-- url     : https://prove2.me/theorems/d5d4be96-d0da-475c-9926-5992537c8de5
-- title:
--   Neg: rep all
-- statement:
--   The Neg construction uses the rep all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L126-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L126-L135

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

theorem Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_all (q d : ℕ) (hq : q.Prime) (hd : d.Prime) (hq8 : q % 8 = 3) (hqd : q ≠ d) (m : ℕ) :
    0 < m → Rep q d m := by sorry
