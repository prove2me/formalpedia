-- Prove2me | Theorems.Thm_ClusterDecomp_fair_cut_time
-- name    : ClusterDecomp.fair_cut_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:10:35.662207+00:00
-- url     : https://prove2.me/theorems/3cf6bc80-101a-43cd-93dd-3ffee4ff3ecd
-- title:
--   [LL25] black box, p.9 — a $(1+\eta)$-fair $s,t$-cut in $\widetilde O(m/\eta)$ time
-- statement:
--   Let $H$ be an undirected capacitated graph with terminals $s,t$, $n\ge2$ vertices, $m\ge1$ edges and capacities of polynomial ratio, and let $0<\eta\le1$. A $(1+\eta)$-fair $s,t$-cut can be computed in $\widetilde O(m/\eta)$ time. Precisely: for every $a$ there are one program $P$ and an exponent $c$, and for every $d$ a constant $C>0$, such that on all such inputs with capacity ratio at most $n^d$, on every tape $P$ halts within
--   $$C\,\frac{m}{\eta}\,\log^cn$$
--   steps, and on a measurable set of tapes of probability at least $1-n^{-a}$ the output is a $(1+\eta)$-fair $s,t$-cut.
--
--   This is the only algorithmic primitive of Algorithms 1 and 2, which the paper uses as a black box with $\eta=\varepsilon/16$ and $\eta=1/h$.
--
--   **Formalization Note** This is what the present paper says of [LL25]; that paper's own statement was not consulted.
--
--   Differences from the source:
--   - reading: "runs in Õ(·) time", with no machine named → one finite admissible program of ClusterDecomp.Machine; reason: the paper names no machine; a small machine with no free computation gives the strongest reading, and a cost monad under ∃ would make the claim trivial
--   - reading: "randomized algorithm", with no failure probability printed → for every a, a program with worst-case time on every tape and a measurable set of tapes of probability at least 1 − n^{−a} on which the output is correct; reason: literal no-failure would be a deterministic algorithm, which the paper does not supply; a constant success probability would be the weaker reading
--   - reading: a (1+η)-fair cut in Õ(m/η) time, with η unrestricted → 0 < η ≤ 1; reason: the printed form is false for huge η, since any correct program must read Θ(m) input while m/η → 0; the paper uses only η = ε/16 and η = 1/h, both at most 1
--   - reading: the graph of the black box → positive real capacities of ratio at most n^d, no parallel edges, n ≥ 2, m ≥ 1; reason: the capacity ratio is the standing assumption of p.1 ("Throughout the paper … the ratio between the maximum weight of any edge and the minimum one is upper bounded by a polynomial in n"), read for every graph the black box is run on, with d quantified after the program as in the goal; capacities are real because β·deg(v) is real in Algorithm 1; zero capacities are left out of the list, and m = 0 is trivial for the caller
--   - encoding: Õ hides log^c n "for a positive constant c" (footnote 2) → ∃ c : ℕ, so c = 0 is allowed; reason: n ≥ 2, so log n ≥ log 2 > 0 and a bound with exponent c gives one with c + 1 after replacing C by C / log 2; the two readings are equivalent
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), §3, p.9 (PDF p.11), citing [LL25]

import Mathlib
import Definitions.Def_ClusterDecomp_Instance
import Definitions.Def_ClusterDecomp_IsFairCut

open Finset
open scoped ENNReal

namespace ClusterDecomp

/-- **[LL25] black box.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), §3, p.9 (PDF p.11).

"It is known that a (1 + η)-fair s, t-cut can be computed in Õ(m/η) time [LL25], and this algorithm will be used as a black
box in our analysis."

For every `a` there are one admissible program `P` and `c`, and for every `d` a constant `C > 0`, such that on any `n ≥ 2`
vertices (`s` = vertex `0`, `t` = vertex `1`), `m ≥ 1` edges without parallels, positive real capacities of ratio at most
`n^d` and `η ∈ (0, 1]`: on every tape `P` halts with `work ≤ C·(m/η)·(log n)^c`, and on a measurable set of tapes of probability
at least `1 − n^{−a}` its output is a `(1+η)`-fair `s,t`-cut.

**Formalization Note.**
* This is what this paper says of [LL25]; [LL25] itself was not read. Its failure probability is not printed, and `n^{−a}`
  is the reading used for the goal.
* `η ≤ 1`: the printed bound is false for huge `η`, since `m/η → 0` while the input must be read. The paper uses only
  `η = ε/16` and `η = 1/h`.
* Capacities are real because `β·deg(v)` is real in Algorithm 1. Zero capacities are left out of the list. -/
theorem fair_cut_time :
    ∀ a : ℕ, ∃ P : Program, Admissible P ∧ ∃ c : ℕ, ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) (hn : 2 ≤ n) (e : Fin m → Fin n × Fin n) (cap : Fin m → ℝ) (η : ℝ),
        1 ≤ m → Function.Injective (fun j => s((e j).1, (e j).2)) →
        (∀ j, 0 < cap j) → (∀ j j', cap j ≤ (n : ℝ) ^ d * cap j') → 0 < η → η ≤ 1 →
        (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P (fairCutInput n e cap η) ω t).halted = true ∧
          ((run P (fairCutInput n e cap η) ω t).work : ℝ) ≤
            C * ((m : ℝ) / η) * Real.log n ^ c) ∧
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - 1 / (n : ℝ) ^ a ≤ (coinTape E).toReal ∧
          ∀ ω ∈ E, ∀ t : ℕ, (run P (fairCutInput n e cap η) ω t).halted = true →
            IsFairCut (edgeWeight e cap) (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n)
              (fairCutOutput n (run P (fairCutInput n e cap η) ω t)) (1 + η) := by sorry

end ClusterDecomp
