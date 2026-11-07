-- Prove2me | Theorems.Thm_DisjointPathsDAG_theorem_4_7
-- name    : DisjointPathsDAG.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:04.614692+00:00
-- url     : https://prove2.me/theorems/830b4e27-45b0-4fe8-9528-e4b0a9a3ba6c
-- title:
--   Theorem 4.7 — $k$-DSP and $k$-DP in DAGs in expected time $O_k(m+n^{k-3+\omega+\varepsilon})$
-- statement:
--   Let $\omega$ be the exponent of matrix multiplication by bilinear algorithms over $\mathbb F_2$, and put $\beta=k-3+\omega+\varepsilon$. For every $k\ge3$ and $\varepsilon>0$ there is a constant $C$ such that for every $c>0$ there are randomized algorithms on the word RAM with $\Theta(\log(m+n))$-bit words, exact real additions and comparisons, and a field $\mathbb F_{2^q}$ with $q=O(\log(m+n))$, such that on every DAG with $n$ vertices, $m$ edges (parallel edges allowed), real edge weights (negative allowed) and $k$ terminal pairs ($s_i=t_i$ allowed):
--
--   1. **k-DSP, reporting.** The expected running time is at most $C\,(m+n^\beta)$. The algorithm never returns an invalid tuple, returns "no" on every infeasible instance, and reports a k-DSP solution with probability at least $1-n^{-c}$ on every feasible instance.
--   2. **k-DSP, decision.** On every run the running time is at most $C\,(m+n^\beta)$; the answer is never "yes" on an infeasible instance, and is "yes" with probability at least $1-n^{-c}$ on a feasible one.
--   3. **k-DP.** The same two guarantees hold for the k vertex-disjoint paths problem on DAGs.
--
--   With $\omega<2.372$ this is $O_k(m+n^{k-0.62})$, below the $O_k(mn^{k-1})$ pebbling bound for every $k\ge3$.
--
--   **Formalization Note** The word width is $A\lceil\log_2(n+m+2)\rceil$ and the field is $\mathbb F_{2^{q(n+m)}}$ with $q(N)\le A\lceil\log_2(N+2)\rceil$, for $A$ and $q$ chosen with the programs.
--
--   Differences from the source:
--   - reading: "Fix k ≥ 3 and c > 0 … in expected Ok(m + n^{k−3+ω+ε}) time, for every fixed ε > 0" → $C$ depends only on $(k,\varepsilon)$ and serves every $c>0$; reason: the stronger reading; field operations cost one step at every field size
--   - reading: "for every fixed ε > 0" → $\varepsilon$ is chosen before the programs: one program per $(k,\varepsilon,c)$, uniform in $n$ and $m$; reason: the algorithm is uniform; $\omega$ gives a fixed base bilinear algorithm per $\varepsilon$
--   - reading: $\Theta(\log(m+n))$-bit words and $\mathbb F_{2^q}$ with $q=\Theta(\log(m+n))$ → existential $A\ge1$ and $q$ with word width `wordWidth A (n + m)` and $q(N)\le A\lceil\log_2(N+2)\rceil$; reason: upper bounds only; a lower bound on $q$ is not imposed, since a smaller field only hurts the algorithm
--   - encoding: the model of Section 2.1, $\mathbb F_{2^q}$, $n^{\beta}$, paths → the machine `DisjointPathsDAG.Machine`, its input/output layout, `GaloisField 2 (q (n + m))`, `Real.rpow`, paths as edge lists; reason: Lean conventions; same instances
--   - encoding: "These guarantees also hold for k-DP in DAGs" → two further programs for k-DP on unweighted inputs; reason: k-DP inputs carry no weights
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 4.7, p.21 (formal version of Theorem 1.1, p.2); Section 2.1, p.6

import Mathlib
import Definitions.Def_DisjointPathsDAG_Encoding
import Definitions.Def_mme_omega

set_option autoImplicit false

namespace DisjointPathsDAG

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 4.7 (Disjoint paths in DAGs, formal
version of Theorem 1.1), p.21: "Fix k ≥ 3 and c > 0. On a DAG with n vertices, m edges, and real edge
weights, k-DSP can be solved by a randomized algorithm in expected Ok(m + nk−3+ω+ε) time, for every
fixed ε > 0. The algorithm never returns an invalid tuple, returns no on every infeasible instance, and
reports a solution with probability at least 1 − n−c on every feasible instance. Decision with the same
one-sided error has the same worst-case time bound. These guarantees also hold for k-DP in DAGs."

With `ω = MME.matMulExp (ZMod 2)` and `β := k − 3 + ω + ε`: for every `k ≥ 3` and `ε > 0` there is a
constant `C > 0` such that for every `c > 0` there are a word-width constant `A ≥ 1`, a field-size
function `q` with `q(N) ≤ A · ⌈log₂(N + 2)⌉`, and four machine programs such that, on every DAG with `n`
vertices, `m` edges (parallel edges allowed), real edge weights (negative allowed) and `k` terminal pairs
(`sᵢ = tᵢ` allowed), run with words of `A · ⌈log₂(n + m + 2)⌉` bits and the field `F_{2^{q(n+m)}}`:
1. (k-DSP, reporting) the expected running time is at most `C (m + n^β)`, every halting run returns "no"
   or a k-DSP solution, it returns "no" on every infeasible instance, and on a feasible instance it
   returns a solution with probability at least `1 − n^(−c)`;
2. (k-DSP, decision) on every tape the running time is at most `C (m + n^β)`, it never answers "yes" on
   an infeasible instance, and on a feasible one it answers "yes" with probability at least `1 − n^(−c)`;
3. (k-DP) the same two guarantees for the k vertex-disjoint paths problem on the unweighted DAG.

**Formalization Note** The machine is `DisjointPathsDAG.Machine` (unit cost per instruction; words
modulo `2^w`; reals with `+`, `−`, `<`, `=` only; a field bank with uniform sampling); the input and
output layouts are those of `DisjointPathsDAG.Encoding`. `C` depends only on `k` and `ε`, and is chosen
before the error exponent `c`; the programs, `A` and `q` depend on `k`, `ε`, `c` and are uniform in
`n`, `m`. `n^β` is `Real.rpow`. -/
theorem theorem_4_7 :
    ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
      ∃ (A : ℕ) (q : ℕ → ℕ) (Prep Pdec Qrep Qdec : Program), 1 ≤ A ∧
        (∀ N : ℕ, q N ≤ A * Nat.clog 2 (N + 2)) ∧
        (∀ (n m : ℕ) (G : Digraph n m) (wt : Fin m → ℝ) (pairs : Fin k → Fin n × Fin n),
          G.IsAcyclic →
          ReportsWithin k Prep (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
            (encodeDSP (GaloisField 2 (q (n + m))) G wt pairs)
            (C * ((m : ℝ) + (n : ℝ) ^ ((k : ℝ) - 3 + MME.matMulExp (ZMod 2) + ε)))
            (liftSol (IsDSPSolution G wt pairs)) (DSPFeasible G wt pairs) (1 - (n : ℝ) ^ (-c)) ∧
          DecidesWithin Pdec (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
            (encodeDSP (GaloisField 2 (q (n + m))) G wt pairs)
            (C * ((m : ℝ) + (n : ℝ) ^ ((k : ℝ) - 3 + MME.matMulExp (ZMod 2) + ε)))
            (DSPFeasible G wt pairs) (1 - (n : ℝ) ^ (-c))) ∧
        (∀ (n m : ℕ) (G : Digraph n m) (pairs : Fin k → Fin n × Fin n), G.IsAcyclic →
          ReportsWithin k Qrep (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
            (encodeDP (GaloisField 2 (q (n + m))) G pairs)
            (C * ((m : ℝ) + (n : ℝ) ^ ((k : ℝ) - 3 + MME.matMulExp (ZMod 2) + ε)))
            (liftSol (IsDPSolution G pairs)) (DPFeasible G pairs) (1 - (n : ℝ) ^ (-c)) ∧
          DecidesWithin Qdec (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
            (encodeDP (GaloisField 2 (q (n + m))) G pairs)
            (C * ((m : ℝ) + (n : ℝ) ^ ((k : ℝ) - 3 + MME.matMulExp (ZMod 2) + ε)))
            (DPFeasible G pairs) (1 - (n : ℝ) ^ (-c))) := by sorry

end DisjointPathsDAG
