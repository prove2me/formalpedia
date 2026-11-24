-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_lseries_taylor_lower_bound
-- name    : Formalism.ZeroFreeDirichlet.lseries_taylor_lower_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:43:03.389752+00:00
-- url     : https://prove2.me/theorems/d449c5ba-4f9d-47ea-b3cb-0d2ca6ddd840
-- title:
--   Zero Free Dirichlet: lseries taylor lower bound
-- statement:
--   The Zero Free Dirichlet construction uses the lseries taylor lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean#L30-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/IteratedDerivLseriesAlternatingNonneg.lean#L30-L151

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivInvSubOneAtTwo
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivLseriesAlternatingNonneg
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

theorem Formalism.ZeroFreeDirichlet.lseries_taylor_lower_bound {a : ℕ → ℂ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : a 1 = 1)
    (habs : LSeries.abscissaOfAbsConv a ≤ 1) {F G : ℂ → ℂ} {lam : ℂ} (hG : Differentiable ℂ G)
    (hF : ∀ s : ℂ, 1 < s.re → F s = LSeries a s) (hFG : ∀ s : ℂ, s ≠ 1 → F s = G s + lam / (s - 1))
    {B : ℝ} (hB : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖G s‖ ≤ B) {σ : ℝ} (hσ1 : 7 / 8 ≤ σ)
    (hσ2 : σ < 1) {M : ℕ} (hM : 1 ≤ M) :
    1 - ‖lam‖ * (2 - σ) ^ M / (1 - σ) - 4 * B * (3 / 4) ^ M ≤ (F σ).re := by sorry
