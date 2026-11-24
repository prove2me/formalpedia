-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_two_sub_pow_le_exp
-- name    : Formalism.ZeroFreeDirichlet.two_sub_pow_le_exp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:44:33.290607+00:00
-- url     : https://prove2.me/theorems/1a4ef8f8-2f40-4883-8502-93cb2e31b51f
-- title:
--   Zero Free Dirichlet: two sub pow le exp
-- statement:
--   The Zero Free Dirichlet construction uses the two sub pow le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean#L47-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqKeyOf.lean#L47-L58

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivLseriesAlternatingNonneg
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqKeyOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexOrder Nat
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.two_sub_pow_le_exp {A P σ : ℝ} {M : ℕ} (hA : 0 ≤ A) (hσ1 : 7 / 8 ≤ σ) (hσ2 : σ < 1)
    (hM : (M : ℝ) ≤ A + P) : (2 - σ) ^ M ≤ Real.exp A * Real.exp (P * (1 - σ)) := by sorry
