-- Prove2me | Theorems.Thm_ClusterDecomp_theorem_1_1
-- name    : ClusterDecomp.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:10:19.800887+00:00
-- url     : https://prove2.me/theorems/e0f1b362-f284-441d-bffb-70e74e6460fa
-- title:
--   Theorem 1.1, p.2 — backbones in $\widetilde O(m/\varepsilon)$ and a partition in $\widetilde O(m(\varepsilon^{-1}+\log^2k))$ time, with inner and outer conductance guarantees
-- statement:
--   Let $G=(V,E,w)$ be a graph with $n$ vertices and $m$ edges, positive integer weights of polynomial ratio, and every vertex of positive degree. Let $k\ge2$, $0<\varepsilon\le1$, $p>0$, and let $A_1,\dots,A_k$ be pairwise disjoint nonempty subsets of positive volume with $\phi_G(A_i)\le p$ for every $i$, and $\rho_G(k+1)\ge(1+\varepsilon)p$. Then:
--
--   1. There is a randomized algorithm running in $\widetilde O(m/\varepsilon)$ time that outputs pairwise disjoint $B_1,\dots,B_k$ with $B_i\subseteq A_i$ and, for every $i$,
--   $$\phi_G(B_i)\le\Bigl(1+\frac{\varepsilon}{16}\Bigr)p,\qquad \phi(G\{B_i\})\ge\frac{\varepsilon\,\rho_G(k+1)}{9}.$$
--   2. There is a randomized algorithm running in $\widetilde O(m(\varepsilon^{-1}+\log^2k))$ time that outputs a partition $V=P_1\sqcup\dots\sqcup P_k$ with, for every $i$,
--   $$\phi_G(P_i)\le4kp,\qquad \phi(G\{P_i\})\ge\frac{\varepsilon\,\rho_G(k+1)}{53k}.$$
--
--   Here $\widetilde O$ hides a factor $\log^cn$. Precisely: for every $a$ there are one program $P$ and an exponent $c$, and for every $d$ a constant $C>0$, such that on all instances with weight ratio at most $n^d$, on every tape $P$ halts within $C\,(m/\varepsilon)\log^cn$, respectively $C\,m(1/\varepsilon+\log^2k)\log^cn$, steps, and the guarantees hold on a measurable set of tapes of probability at least $1-n^{-a}$.
--
--   This is the first nearly-linear time algorithm known to produce a partition into expanders with both inner and outer conductance guarantees, starting from arbitrary low-conductance sets.
--
--   Differences from the source:
--   - reading: "runs in Õ(·) time", with no machine named → one finite admissible program of the randomized exact-arithmetic real RAM ClusterDecomp.Machine: rational literals, + − × ÷, integer pointers with + −, integer memory, a pointer-to-real cast, fair coins, unit cost; no floor, real-to-integer cast, sqrt, exp, log; reason: the paper names no machine; a small machine with no free computation gives the strongest reading, and a cost monad under ∃ would make the claim trivial
--   - reading: "randomized algorithm", with no failure probability printed → for every a, a program with worst-case time on every tape and a measurable set of tapes of probability at least 1 − n^{−a} on which the output is correct; reason: literal no-failure would be a deterministic algorithm, which the paper does not supply; a constant success probability would be the weaker reading
--   - reading: Õ hides log^c n (footnote 2); weight ratio polynomial in n (p.1) → ∀a ∃P ∃c ∀d ∃C > 0 ∀instance with w_j ≤ n^d w_j′: work ≤ C·(m/ε)·(log n)^c, resp. C·m·(1/ε + (log k)²)·(log n)^c, with no log(1/ε), log(1/p) or bit length; reason: Algorithm 1 takes no degree d as input, so the program and c do not know d; the instance comes last, or the program could be a lookup table; ε, p are inputs
--   - encoding: ϕ(G{B_i}), ρ_G(k+1) as real minima → values in ℝ≥0∞ with ⊤ on an empty family (a singleton S; k equal to the number of vertices); reason: the printed minima are undefined there; ε > 0 gives ε·⊤ = ⊤, and .toReal is never applied, so the bound stays meaningful
--   - generalization: B_i and P_i are not stated to have positive volume → 0 < vol(B_i) and 0 < vol(P_i) are conclusion clauses; reason: ϕ_G needs positive volume and Lemma 3.2 proves it; a stronger conclusion
--   - encoding: G = (V, E, w), A_i ⊆ V, "outputs" sets → an edge list without parallel edges, positive natural weights, A_i as labels in integer memory, output sets as labels at cells −1 − v; reason: the paper names no format, and the bound pays for reading the list
--   - encoding: Õ hides log^c n "for a positive constant c" (footnote 2) → ∃ c : ℕ, so c = 0 is allowed; reason: n ≥ 2, so log n ≥ log 2 > 0 and a bound with exponent c gives one with c + 1 after replacing C by C / log 2; the two readings are equivalent
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Theorem 1.1, p.2 (PDF p.4); definitions and standing assumption, p.1 (PDF p.3); footnote 2, p.2

import Mathlib
import Definitions.Def_ClusterDecomp_Instance

open Finset

namespace ClusterDecomp

/-- **Theorem 1.1.**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027 submission
(manuscript sha256 ba091f54…), Theorem 1.1, p.2 (PDF p.4); definitions and standing assumption, p.1 (PDF p.3); footnote 2, p.2.

"Theorem 1.1. Let k ≥ 2, 0 < ε ≤ 1, and p > 0. Suppose that A1, . . . , Ak are pairwise disjoint, nonempty, positive-volume subsets of V satisfying ϕG(Ai) ≤ p for every i ∈ [k], and
ρG(k + 1) ≥ (1 + ε)p. Then, (i) there is a randomized algorithm (Algorithm 1) that runs in Õ(m/ε) time and outputs k pairwise disjoint subsets B1, . . . , Bk (with Bi ⊆ Ai for all i ∈ [k]) such that
it holds for every i ∈ [k] that ϕG(Bi) ≤ (1 + ε/16) p and ϕ(G{Bi}) ≥ ερG(k + 1)/9; (ii) there is a randomized algorithm (formed by Algorithms 1 and 2) that runs in Õ(m(ε−1 + log2 k)) time and outputs
a partition V = P1 ⊔ · · · ⊔ Pk such that it holds for every i ∈ [k] that ϕG(Pi) ≤ 4kp and ϕ(G{Pi}) ≥ ερG(k + 1)/(53k)."

A conjunction of the two parts, each with its own program. For every `a` there are one admissible program `P` and `c`, and for every `d` a constant `C > 0`, such that on every instance whose weights have
ratio at most `n^d`:
* on every coin tape, `P` halts with `work ≤ C·(m/ε)·(log n)^c`, respectively `C·m·(1/ε + (log k)²)·(log n)^c`;
* on a measurable set of tapes of probability at least `1 − n^{−a}`, the output has the guarantee.

**Formalization Note.**
* The paper names no machine, so the time bound is on the deep machine `ClusterDecomp.Machine`: the program is a finite list, and the program and `c` do not know `d`, since Algorithm 1 takes no such input.
* The paper prints no failure probability. "Randomized" is read as failure at most `n^{−a}` for every `a`, with worst-case time on every tape.
* `ρ` and `ϕ` are in `ℝ≥0∞`; `.toReal` is never applied to them. At `k = n`, `ρ_G(k+1) = ⊤`, each output set is a singleton and its inner conductance is `⊤`.
* Each output set is also stated to have positive volume, which the conductances need.
* `k ≥ 2` and disjoint nonempty sets force `n ≥ 2`, and positive degree forces `m ≥ 1`, so `log n > 0` and the bound is positive. -/
theorem theorem_1_1 :
    (∀ a : ℕ, ∃ P : Program, Admissible P ∧ ∃ c : ℕ, ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ I : Instance, I.Hyp d →
        (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P I.input ω t).halted = true ∧
          ((run P I.input ω t).work : ℝ) ≤ C * ((I.m : ℝ) / I.ε) * Real.log I.n ^ c) ∧
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - 1 / (I.n : ℝ) ^ a ≤ (coinTape E).toReal ∧
          ∀ ω ∈ E, ∀ t : ℕ, (run P I.input ω t).halted = true →
            ∀ B : Fin I.k → Finset (Fin I.n), B = outputSet I.n (run P I.input ω t) →
              (Pairwise fun i j => Disjoint (B i) (B j)) ∧
              ∀ i, B i ⊆ I.A i ∧ 0 < I.graph.vol (B i) ∧
                I.graph.phiOut (B i) ≤ (1 + I.ε / 16) * I.p ∧
                ENNReal.ofReal (I.ε / 9) * I.graph.rho (I.k + 1) ≤
                  (I.graph.degPres (B i)).phi) ∧
    (∀ a : ℕ, ∃ P : Program, Admissible P ∧ ∃ c : ℕ, ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ I : Instance, I.Hyp d →
        (∀ ω : ℕ → Bool, ∃ t : ℕ, (run P I.input ω t).halted = true ∧
          ((run P I.input ω t).work : ℝ) ≤
            C * I.m * (1 / I.ε + Real.log I.k ^ 2) * Real.log I.n ^ c) ∧
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ 1 - 1 / (I.n : ℝ) ^ a ≤ (coinTape E).toReal ∧
          ∀ ω ∈ E, ∀ t : ℕ, (run P I.input ω t).halted = true →
            ∀ Q : Fin I.k → Finset (Fin I.n), Q = outputSet I.n (run P I.input ω t) →
              (∀ v : Fin I.n, ∃ i : Fin I.k, v ∈ Q i) ∧
              (Pairwise fun i j => Disjoint (Q i) (Q j)) ∧
              ∀ i, 0 < I.graph.vol (Q i) ∧
                I.graph.phiOut (Q i) ≤ 4 * I.k * I.p ∧
                ENNReal.ofReal (I.ε / (53 * I.k)) * I.graph.rho (I.k + 1) ≤
                  (I.graph.degPres (Q i)).phi) := by sorry

end ClusterDecomp
