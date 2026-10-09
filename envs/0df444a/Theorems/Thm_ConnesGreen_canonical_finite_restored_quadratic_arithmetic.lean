-- Prove2me | Theorems.Thm_ConnesGreen_canonical_finite_restored_quadratic_arithmetic
-- name    : ConnesGreen.canonical_finite_restored_quadratic_arithmetic
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T14:09:50.06714+00:00
-- url     : https://prove2.me/theorems/b188d2dd-5145-42d0-967d-f1713b001112
-- title:
--   Original finite-restored denominator has its exact full arithmetic test value
-- statement:
--   For every original positive support window, actual finite restoration packet $F$, real regularization $\varepsilon$, and original supported test $g$, with $x=\operatorname{sourceEmbed}(\operatorname{problemOneL}(g))$, we prove
--   $$\operatorname{Re}\langle(PP^*+\varepsilon I-B_FB_F^*)x,x\rangle
--   =\operatorname{Re}W(g*\operatorname{starInv}(g))+\|M_F^*x\|^2+\varepsilon E(g),$$
--   where E(g) is EXACTLY the original physicalTestEnergy integral of |g prime| squared plus one quarter of |g| squared. The public expression unfolds that unchanged definition; the native signature is checked by definitional conversion. Accepted full signed actor arithmetic and a closed convergent full selected/complementary negative-analysis partition identify positive minus complementary analysis energy with the complete Weil value plus restored selected energy. Adjoint norm-square identities give the denominator quadratic form. Accepted exact original physical test norm supplies the regularization contribution. The statement permits EVERY real epsilon; it does not assume denominator positivity or any endpoint estimate, and the complete actual-zero complement is retained.
-- source:
--   monocap-tech/weil native head a1a3c6481eb9bc50bc7e92aa694f6ae530c7e359; unchanged MarkerQuadratic.lean and CanonicalGreenQuadraticEndpoint.lean declarations; explicit native definitional unfoldings only

import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability WeilDefect.WDT13
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_finite_restored_quadratic_arithmetic (t : ℝ) (ht : 0 < t)
    (F : Finset CriticalZeros) (ε : ℝ) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    RCLike.re ⟪(canonicalPositiveCovariance t ht + ε • 1 - canonicalTailCovariance t ht F)
      (sourceEmbed t (problemOneL g)), sourceEmbed t (problemOneL g)⟫_ℂ =
      (weilDistribution (conv g (starInv g))).re +
      ‖(canonicalSelectedSynthesis t ht F).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
      ε * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)) := by sorry
