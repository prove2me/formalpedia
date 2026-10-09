-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenCount_theorem_10
-- name    : EvenCycleTuran.EvenCount.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:07.751337+00:00
-- url     : https://prove2.me/theorems/680e5431-5492-43da-903e-f71c53f8cc8d
-- title:
--   Theorem 10 — ex(n, C_{2l}, C_{2k}) ≤ (1+o(1))2^{l−2}(k−1)^l n^l/(2l); ≥ (1+o(1))(k−1)_l n^l/(2l) (k > l); ≥ (1+o(1))n^l/l^l (l > k ≥ 3)
-- statement:
--   Let $\mathrm{ex}(n,C_{2l},C_{2k})$ be the maximum number of copies of the cycle $C_{2l}$ in a graph on $n$ vertices containing no $C_{2k}$, and let $(m)_l=m(m-1)\cdots(m-l+1)$ be the falling factorial. As $n\to\infty$ with $k,l$ fixed:
--
--   1. for any $l\ge3$ and $k\ge2$,
--   $$\mathrm{ex}(n,C_{2l},C_{2k})\le(1+o(1))\frac{2^{l-2}(k-1)^l}{2l}n^l;$$
--   2. for any $k>l\ge2$,
--   $$\mathrm{ex}(n,C_{2l},C_{2k})\ge(1+o(1))\frac{(k-1)_l}{2l}n^l;$$
--   3. for any $l>k\ge3$,
--   $$\mathrm{ex}(n,C_{2l},C_{2k})\ge(1+o(1))\frac1{l^l}n^l.$$
--
--   With Theorem 11 this determines the order of magnitude $\Theta(n^l)$ of $\mathrm{ex}(n,C_{2l},C_{2k})$ for all $k,l\ge2$ except the lower bound at $k=2$.
--
--   **Formalization Note** Each "$(1+o(1))$" is a function $\varepsilon(n)\to0$ depending only on $k$ and $l$, with the bound holding for all sufficiently large $n$. Copies are unlabelled (`copyCount`), and $(k-1)_l$ is `Nat.descFactorial (k - 1) l`. The three parameter ranges are those of the page.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 5, Theorem 10

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenCount_Setting

namespace EvenCycleTuran.EvenCount
open Finset SimpleGraph Filter Topology

theorem theorem_10 :
    (∀ l k : ℕ, 3 ≤ l → 2 ≤ k → ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        (EvenCycleTuran.C4Count.exCyc n (cycleGraph (2 * l)) {2 * k} : ℝ) ≤
          (1 + ε n) * ((2 : ℝ) ^ (l - 2) * ((k : ℝ) - 1) ^ l / (2 * l) * (n : ℝ) ^ l)) ∧
    (∀ l k : ℕ, 2 ≤ l → l < k → ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        (EvenCycleTuran.C4Count.exCyc n (cycleGraph (2 * l)) {2 * k} : ℝ) ≥
          (1 + ε n) * (((k - 1).descFactorial l : ℝ) / (2 * l) * (n : ℝ) ^ l)) ∧
    (∀ l k : ℕ, 3 ≤ k → k < l → ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        (EvenCycleTuran.C4Count.exCyc n (cycleGraph (2 * l)) {2 * k} : ℝ) ≥
          (1 + ε n) * (1 / (l : ℝ) ^ l * (n : ℝ) ^ l)) := by sorry

end EvenCycleTuran.EvenCount
