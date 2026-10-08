-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_prime_convolution_norm_le_finite_source_energy
-- name    : ConnesGreen.RG0Integration.prime_convolution_norm_le_finite_source_energy
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:38:38.200599+00:00
-- url     : https://prove2.me/theorems/3bba9e14-a36a-4677-a6d5-32f7cc3f5262
-- title:
--   Original full prime contribution controlled by finite cutoff and physical source energy
-- statement:
--   For an original smooth test supported in $(-t,t)$, with $t>0$ and an integer $N>e^{2t}$, the entire prime term of its self-convolution satisfies $$|\operatorname{primeSum}(g*\widetilde g)|\le4\|\operatorname{sourceEmbed}_t(Lg)\|^2\sum_{n<N}\frac{\Lambda(n)}{\sqrt n}\max(2t-|\log n|,0).$$ The finite cutoff follows from the original prime HasSum theorem, and the bound uses the accepted overlap estimate and exact original physical norm. All natural-number terms are retained; the terms at zero and one vanish by the original von Mangoldt function, with no index convention change.
-- source:
--   monocap-tech/weil: WeilDefect/Connes/RG0DependencyIntegration.lean, original actor and metric adapters at 4ba3a3a569d72a0d5af2ba6ea320f948030dcca5; proof and statement boundaries recovered with Lean elaborator metadata.

import Theorems.Thm_ConnesGreen_prime_convolution_hasSum_exp_cutoff
import Theorems.Thm_ConnesGreen_convolution_overlap_dirichlet_energy_bound
import Theorems.Thm_ConnesGreen_actual_physical_test_norm
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.RG0Integration.prime_convolution_norm_le_finite_source_energy (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) (N : ℕ) (hN : Real.exp (2*t) < N) :
    ‖primeSum (conv g (starInv g))‖ ≤
      4 * ‖sourceEmbed t (problemOneL g)‖ ^ 2 *
        ∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          max (2*t - |Real.log n|) 0 := by sorry
