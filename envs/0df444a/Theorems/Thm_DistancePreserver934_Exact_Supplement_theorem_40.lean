-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_theorem_40
-- name    : DistancePreserver934.Exact.Supplement.theorem_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:29:54.218027+00:00
-- url     : https://prove2.me/theorems/cffd42be-9371-423a-801f-803162188d74
-- title:
--   Theorem 40 — The full complete-sourcewise +2k family, k≥2, with its source-size range
-- statement:
--   For each fixed integer $k\ge2$ there is $C_k>0$, independent of the graph and source set, such that every source set $S$ of size $\sigma\le n^{(2k-1)/(3k)}$ admits a complete sourcewise additive $+2k$ spanner with
--
--   $$|E(J)|\le C_k\bigl(n+n^{(8+8k)/(5+8k)}\sigma^{4k/(5+8k)}\bigr).$$
--
--   Both examples are included explicitly: at $k=2$, $|E(J)|\le C_2(n+n^{8/7}\sigma^{8/21})$ when $\sigma\le n^{1/2}$; at $k=3$, $|E(J)|\le C_3(n+n^{32/29}\sigma^{12/29})$ when $\sigma\le n^{5/9}$. The spanner preserves every reachable ordered source pair, including pairs absent from any selected partial demand set. Empty source sets, small graphs and disconnected graphs remain in the statement. This companion family uses Theorem 37 and Lemma 39.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: O_k coefficients and the complete-sourcewise family with two examples → for every natural k≥2 a positive coefficient before all graph data, with the family and explicit k=2,3 consequences in one conjunction; reason: the source coefficient may depend only on k; real subtraction and division preserve the full threshold and exponents
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Theorem 40, printed p. 34 (PDF p. 35)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem theorem_40 :

  ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V),
    let n := (Fintype.card V : ℝ)
    let σ := (S.card : ℝ)
    ((σ ≤ n ^ ((2 * (k : ℝ) - 1) / (3 * (k : ℝ))) →
      ∃ J : SimpleGraph V, IsCompleteSourcewise G J S (2 * k) ∧
        (numEdges J : ℝ) ≤ C * (n + W k n σ)) ∧
    (k = 2 → σ ≤ n ^ ((1 : ℝ) / 2) →
      ∃ J : SimpleGraph V, IsCompleteSourcewise G J S 4 ∧
        (numEdges J : ℝ) ≤ C * (n + n ^ ((8 : ℝ) / 7) * σ ^ ((8 : ℝ) / 21))) ∧
    (k = 3 → σ ≤ n ^ ((5 : ℝ) / 9) →
      ∃ J : SimpleGraph V, IsCompleteSourcewise G J S 6 ∧
        (numEdges J : ℝ) ≤ C * (n + n ^ ((32 : ℝ) / 29) * σ ^ ((12 : ℝ) / 29))))
 := by sorry

end DistancePreserver934.Exact.Supplement
