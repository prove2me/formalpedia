-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_norm_unit
-- name    : Formalism.L2.PairingIndexBounds.Eq.J.Neg.norm_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:32.816796+00:00
-- url     : https://prove2.me/theorems/d8a411e1-ac8c-4866-8ca5-171424367d77
-- title:
--   Neg: norm unit
-- statement:
--   The Neg construction uses the norm unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/SplitPairEquations/IntegralSquareRoots/HenselQuad.lean#L21-L24

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

theorem Formalism.L2.PairingIndexBounds.Eq.J.Neg.norm_unit (p : ℕ) [Fact p.Prime] (k : ℤ) (h : ¬ (p : ℤ) ∣ k) : ‖(k : ℤ_[p])‖ = 1 := by sorry
