-- Prove2me | Theorems.Thm_BlindProphetSec_Upper_theorem_1_3
-- name    : BlindProphetSec.Upper.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:14.463281+00:00
-- url     : https://prove2.me/theorems/aee78905-5e9e-41de-9af6-4558070b3bc1
-- title:
--   Theorem 1.3, p. 4 — no stopping strategy can guarantee a constant better than √3 − 1 ≈ 0.732 in the prophet secretary problem
-- statement:
--   In the **prophet secretary problem** a gambler observes independent nonnegative random variables $V_1,\dots,V_N$ with known laws, presented in a uniformly random order $\sigma$, and must decide online, using only what has been revealed so far (and possibly private randomness), when to stop; she receives the value $V_{\sigma_T}$ at her stopping time $T$, and $0$ if she never stops. A strategy guarantees a constant $c$ if on every instance $\mathbb E(V_{\sigma_T})\ge c\,\mathbb E(\max_i V_i)$.
--
--   **Theorem 1.3.** No strategy can guarantee a constant better than $\sqrt3-1\approx0.732$: for every $c>\sqrt3-1$ there is an instance — a number $N$ and laws of $N$ independent nonnegative variables, with $0<\mathbb E(\max_i V_i)<\infty$ — on which every stopping strategy $T$ satisfies
--   $$\mathbb E(V_{\sigma_T}) < c\cdot \mathbb E\Big(\max_{1\le i\le N} V_i\Big).$$
--
--   Since the gambler knows the distributions, a strategy may be chosen after the instance; hence "no strategy guarantees $c$" means that some instance defeats every strategy (an instance first, then all strategies), which is what is stated. The theorem separates the prophet secretary problem from the i.i.d. prophet inequality, whose optimal constant is about $0.745$.
--
--   **Formalization Note** The strategy class is that of the definitions file: at each time the decision may depend on all identities and values observed so far and on an independent uniform seed, measurably. The conjuncts $\mathbb E(\max)<\infty$ and $\mathbb E(\max)>0$ are a strengthening of the page's statement (the §5 instance satisfies them); they exclude a degenerate instance with infinite or zero prophet value. The instance is not required to have continuous laws: the paper's continuity convention concerns its blind strategies, and the §5 instance has atoms.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 4, Theorem 1.3; proof §5, pp. 18–19

import Mathlib
import Definitions.Def_BlindProphetSec_Upper_Setting

open MeasureTheory Filter Topology

namespace BlindProphetSec.Upper

theorem theorem_1_3 :
    ∀ c : ℝ, Real.sqrt 3 - 1 < c →
      ∃ (N : ℕ) (μ : Fin N → Measure ℝ),
        (∀ i, IsProbabilityMeasure (μ i)) ∧ (∀ i, μ i (Set.Iio 0) = 0) ∧
        BlindProphetSec.Blind.Emax μ ≠ ⊤ ∧ 0 < BlindProphetSec.Blind.Emax μ ∧
        ∀ s : Strategy N, value s μ < ENNReal.ofReal c * BlindProphetSec.Blind.Emax μ := by sorry

end BlindProphetSec.Upper
