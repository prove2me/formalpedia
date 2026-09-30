-- Prove2me | Theorems.Thm_AlgMechDesign_Local_ratio_step
-- name    : AlgMechDesign.Local.ratio_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T20:00:14.353956+00:00
-- url     : https://prove2.me/theorems/c9ce6dc1-c836-41fc-a3b0-aed65396546d
-- title:
--   Theorem 4.12, proof, last step — an agent holding n near-unit tasks against a split allocation
-- statement:
--   Let $n \ge 1$ agents and $k$ tasks be given, $s$ a type vector, $x$ an allocation and $a$ an agent, and let $\delta, \varepsilon \ge 0$. Suppose that
--
--   1. agent $a$ receives exactly $n$ tasks under $x$, $|x^a| = n$;
--   2. $s^a_j \ge 1 - \delta$ for every task $j \in x^a$;
--   3. $s^l_j \le 1 + \delta$ for every agent $l$ and task $j$;
--   4. $s^l_j \le \varepsilon$ for every agent $l \ne a$ and every task $j \in x^l$.
--
--   Then
--   $$
--   g(x, s) \ge n(1 - \delta) \qquad\text{and}\qquad g(y, s) \le 1 + \delta + k\varepsilon \ \text{ for some allocation } y .
--   $$
--
--   This is the counting step that ends the proof of Theorem 4.12: once the allocation at the perturbed type vector is known, splitting agent $a$'s $n$ tasks among the $n$ agents shows that the ratio of make-spans approaches $n$ as $\delta, \varepsilon \to 0$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 181, proof of Theorem 4.12, last paragraph

import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model

namespace AlgMechDesign.Local

open Finset

/-- Proof of Theorem 4.12, p. 181, last step: if agent `a` holds exactly `n` tasks under `x`,
each taking it at least `1 − δ`, every time is at most `1 + δ`, and every other agent's times on
its own tasks are at most `ε`, then the make-span of `x` is at least `n(1 − δ)` while some
allocation (splitting agent `a`'s tasks among the `n` agents) has make-span at most
`1 + δ + kε`. -/
theorem ratio_step {n k : ℕ} [NeZero n] (s : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (a : Fin n)
    (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hcard : (univ.filter (fun j => x j = a)).card = n)
    (hlow : ∀ j, x j = a → 1 - δ ≤ s a j) (hup : ∀ l j, s l j ≤ 1 + δ)
    (hsmall : ∀ l j, l ≠ a → x j = l → s l j ≤ ε) :
    (n : ℝ) * (1 - δ) ≤ makespan s x ∧
      ∃ y : Fin k → Fin n, makespan s y ≤ 1 + δ + k * ε := by sorry

end AlgMechDesign.Local
