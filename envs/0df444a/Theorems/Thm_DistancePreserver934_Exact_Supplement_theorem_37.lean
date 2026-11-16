-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_theorem_37
-- name    : DistancePreserver934.Exact.Supplement.theorem_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:28:44.231636+00:00
-- url     : https://prove2.me/theorems/6a0df753-a186-4a7e-bd62-9518b8faa562
-- title:
--   Theorem 37 — The complete source-sensitive +2k family for every fixed integer k≥1
-- statement:
--   For every integer $k\ge1$ there is $C_k>0$, depending only on $k$, such that any $n$-vertex graph, source set $S$ of size $\sigma$, and ordered $P\subseteq S\times V$ of size $p$ with $p\sigma^k\le n^{1+2k/3}$ admit a source-sensitive additive $+2k$ spanner satisfying
--
--   $$|E(J)|\le C_k(n+F_k(n,\sigma,p)),\qquad F_k=n^{(8+8k)/(9+8k)}(p\sigma^k)^{4/(9+8k)}.$$
--
--   The same statement explicitly retains all three displayed specializations: $k=1$ gives $n^{16/17}(p\sigma)^{4/17}$ for $p\sigma\le n^{5/3}$; $k=2$ gives $n^{24/25}(p\sigma^2)^{4/25}$ for $p\sigma^2\le n^{7/3}$; $k=3$ gives $n^{32/33}(p\sigma^3)^{4/33}$ for $p\sigma^3\le n^3$. Each bound includes the linear $n$ term. No additional $p\le n$ restriction is imposed. Empty sources, arbitrary original demands and disconnected graphs remain included. This is partial source-sensitive preservation, not a claim about every pair in $S\times V$.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: O_k coefficients and the family with its three displayed specializations → for every natural k≥1 a positive coefficient before all graph data, with the family and explicit k=1,2,3 consequences in one conjunction; reason: the constant can depend only on k; casting k before division preserves the rational exponents and full ranges
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Theorem 37, printed p. 32–33 (PDF p. 33–34)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem theorem_37 :

  ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) (P : Finset (V × V)),
    let n := (Fintype.card V : ℝ)
    let σ := (S.card : ℝ)
    let p := (P.card : ℝ)
    SourceDemands S P →
    ((p * σ ^ k ≤ n ^ (1 + 2 * (k : ℝ) / 3) →
      ∃ J : SimpleGraph V, IsSourceSensitive G J S P (2 * k) ∧
        (numEdges J : ℝ) ≤ C * (n + F k n σ p)) ∧
    (k = 1 → p * σ ≤ n ^ ((5 : ℝ) / 3) →
      ∃ J : SimpleGraph V, IsSourceSensitive G J S P 2 ∧
        (numEdges J : ℝ) ≤ C * (n + n ^ ((16 : ℝ) / 17) * (p * σ) ^ ((4 : ℝ) / 17))) ∧
    (k = 2 → p * σ ^ 2 ≤ n ^ ((7 : ℝ) / 3) →
      ∃ J : SimpleGraph V, IsSourceSensitive G J S P 4 ∧
        (numEdges J : ℝ) ≤ C * (n + n ^ ((24 : ℝ) / 25) * (p * σ ^ 2) ^ ((4 : ℝ) / 25))) ∧
    (k = 3 → p * σ ^ 3 ≤ n ^ (3 : ℝ) →
      ∃ J : SimpleGraph V, IsSourceSensitive G J S P 6 ∧
        (numEdges J : ℝ) ≤ C * (n + n ^ ((32 : ℝ) / 33) * (p * σ ^ 3) ^ ((4 : ℝ) / 33))))
 := by sorry

end DistancePreserver934.Exact.Supplement
