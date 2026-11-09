-- Prove2me | Theorems.Thm_FluidGreedyMatching_CliqueBomb_fluid_limit
-- name    : FluidGreedyMatching.CliqueBomb.fluid_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:11.3132+00:00
-- url     : https://prove2.me/theorems/3e7d85bb-2a3f-4ee9-83d8-0902bb16cb59
-- title:
--   Lemma 5.1 — Fluid limit of the Double-Bomb graphs
-- statement:
--   Fix any real $\sigma>0$ and either $\kappa=0$ or $\kappa=1$. Run MRG on the defined Double-Bomb $G_n^{\kappa}(\sigma)$ with $\lfloor\sigma n\rfloor$ satellite pairs. The solution $(h,q)$ of Eq. (5.1), with $h(0)=1$ and $q(0)=\sigma$, has a finite first hub-exhaustion time $s^*>0$ and $q(s^*)>0$. Endpoint values are continuous extensions. Set
--   $$\Lambda_\kappa(\sigma)=\int_0^{s^*}(4h+2q)\,ds+\frac{q(s^*)^2}{\sigma}.$$
--   Then
--   $$\frac{|M_{\rm MRG}(G_n^{\kappa}(\sigma))|}{n}\xrightarrow{\Pr}\Lambda_\kappa(\sigma),\qquad
--   \frac{\mathbb E|M_{\rm MRG}(G_n^{\kappa}(\sigma))|}{\nu(G_n^{\kappa}(\sigma))}
--   \longrightarrow\frac{\Lambda_\kappa(\sigma)}{2+\sigma}.$$
--
--   The statement asserts existence and uniqueness through first exhaustion and integrability of the displayed continuous edge rate. Convergence in probability is the vanishing of every positive-tolerance deviation probability under the actual finite MRG output law. In particular, no stochastic symmetry, ODE approximation, end-phase certificate or numerical inequality is a premise.
--
--   Differences from the source:
--   - encoding: all positive real sigma, two values of kappa and positive integer sizes → a real sigma with positive hypothesis, a Boolean clique flag, and size j+1; reason: false and true represent exactly zero and one and every positive size is retained
--   - encoding: the ODE solution and its finite first zero with continuous endpoint values → existence of a first-exhaustion solution, explicit uniqueness on its interval, and interval integrability as conclusions; reason: these make the named initial-value solution and its integral well posed without assuming finite exhaustion or terminal positivity
--   - encoding: convergence in probability of matching cardinality and convergence of its expected ratio → finite-sum deviation probabilities and expected ratios computed from the recursively defined MRG output PMF; reason: these are the same random output quantities on varying finite sample spaces
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), Lemma 5.1 and Eq. (5.1), pp. 22–23; Section 5 preamble, p. 21

import Mathlib
import Definitions.Def_FluidGreedyMatching_CliqueBomb_DoubleBomb

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology

namespace FluidGreedyMatching.CliqueBomb

/-- Lemma 5.1, pp. 22–23: both clique flags and all positive real satellite densities.
ODE existence, finite first exhaustion and positive terminal satellite density are conclusions. -/
theorem fluid_limit (σ : ℝ) (hσ : 0 < σ) (κ : Bool) :
    ∃ (S : ℝ) (h q : ℝ → ℝ), isFluidSolution σ κ S h q ∧ 0 < q S ∧
      IntervalIntegrable (fun s => 4 * h s + 2 * q s) volume 0 S ∧
      (∀ δ : ℝ, 0 < δ →
        Tendsto (fun n => bombDeviation σ κ n (fluidValue σ S h q) δ) atTop (𝓝 0)) ∧
      Tendsto (bombRatio σ κ) atTop (𝓝 (fluidValue σ S h q / (2 + σ))) ∧
      (∀ (S' : ℝ) (h' q' : ℝ → ℝ), isFluidSolution σ κ S' h' q' →
        S' = S ∧ ∀ s ∈ Set.Icc 0 S, h' s = h s ∧ q' s = q s) := by sorry

end FluidGreedyMatching.CliqueBomb
