-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_remark_5_1_a
-- name    : ArapostathisAC.VanishingDiscount.remark_5_1_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:16:59.280362+00:00
-- url     : https://prove2.me/theorems/0546e9ec-6a84-4284-addf-16be32bd5c2d
-- title:
--   Remark 5.1(a) — a bounded solution of the ACOE satisfies (5.2)
-- statement:
--   Consider the countable-state controlled Markov process of §5, and let $(\rho,h)$ be a solution of the average cost optimality equation (5.1) with $h$ bounded: $|h(i)|\le C$ for all $i\in S$ and some constant $C$. Then for every admissible policy $\pi\in\Pi$ and every initial state $i$, $h(X_t)$ is $P^\pi_i$-integrable for every $t$ and
--   $$\lim_{t\to\infty}\frac1t E^\pi_i h(X_t)=0.$$
--
--   This is what makes Theorem 5.1 applicable to bounded solutions, and in particular to the solution produced by Theorem 5.2.
--
--   **Formalization Note.** The growth condition is stated for all admissible policies, matching the reading of (5.2) used in Theorem 5.1. The solution property is kept as a hypothesis because the paper states the remark for solutions of the ACOE; only the boundedness of $h$ matters.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 300, Remark 5.1(a), first two sentences

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP

open MeasureTheory Filter Topology

namespace ArapostathisAC.VanishingDiscount

theorem remark_5_1_a {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (hsol : ACOE M ρ h) (hbdd : ∃ C, ∀ i, |h i| ≤ C) :
    ∀ π : Policy M, ∀ i,
      (∀ t, Integrable (fun ω : ℕ → ℕ × A => h (ω t).1) (pathMeasure M π i)) ∧
      Tendsto (fun t : ℕ => (∫ ω, h (ω t).1 ∂(pathMeasure M π i)) / t) atTop (𝓝 0) := by sorry

end ArapostathisAC.VanishingDiscount
