-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_10
-- name    : DistancePreserver934.Exact.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:38:58.444632+00:00
-- url     : https://prove2.me/theorems/37f0b359-f24f-491e-80eb-ac7f75279ea9
-- title:
--   Lemma 10 — a large demand batch covered by few nearby vertices (corrected: $|V_H|>0$)
-- statement:
--   Let $H$ be a minimal distance preserver of $(G,R)$, $R$ a demand set, with $0<|V_H|\le n$, $|E_H|\le nd$ and
--   $$|\Lambda_H|\ge\frac{nd}{20},\qquad\lambda_H(q)\ge l\ (q\in R).$$
--   There are absolute constants $c_0>0$, $c_1$, $c_2$ such that for every real $r$ with $6\le r\le\min\{d^2,l\}$ there are $Q\subseteq R$ and $S\subseteq V_H$ such that $S$ covers $Q$ (Definition 8) and
--   $$|Q|\ge c_0\,d^2\sqrt r,\qquad|S|\le c_1\,\frac{|Q|}{d},\qquad\operatorname{diam}_H(S)\le c_2\,r.$$
--
--   The three constants are chosen once, before the instance, and the same $Q,S$ satisfy all three bounds. This is the batch-selection step of the demand-removal procedure (Step 2 of §6.3).
--
--   Differences from the source:
--   - correction: hypotheses |V_H| ≤ n, |E_H| ≤ nd, |Λ_H| ≥ nd/20 (no positivity of the graph size) → additionally V_H ≠ ∅ (0 < |V|); reason: the printed statement fails with G = H empty, R = ∅, n = 0, d = 3, l = r = 6: all stated and standing assumptions hold, but no nonempty V* exists and no Q ⊆ R has positive size. Under the source radius condition (5), n > 0 forces V_H ≠ ∅ by the edge and private-mass bounds, so the chosen correction excludes exactly the same source instances as n > 0. For the generalized Lemma 13 after dropping (5), V_H = ∅, n = 1, d = 0 is an additional counterexample to using n > 0 alone; this second example does not satisfy (5). The goal and its empty-graph instance are unchanged
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 10 (proof in §5.4, printed pp. 18–19), printed p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 10, printed p.14 / PDF p.15, corrected by requiring `V_H ≠ ∅`.  Let `H` be a minimal
distance preserver of `(G, R)` with `|V_H| ≤ n`, `|E_H| ≤ nd`, `|Λ_H| ≥ nd/20` and `λ_H(q) ≥ l`
for every `q ∈ R`.  For every real `6 ≤ r ≤ min{d², l}` there are `Q ⊆ R` and `S ⊆ V_H` such that
`S` covers `Q`, `|Q| ≥ c₀ d² √r`, `|S| ≤ c₁ |Q| / d` and `diam_H(S) ≤ c₂ r`, for absolute
constants `c₀ > 0, c₁, c₂`. -/
theorem lemma_10 : ∃ c₀ c₁ c₂ : ℝ, 0 < c₀ ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V)) (n : ℕ) (d l r : ℝ),
      0 < Fintype.card V →
      Sec5Context G H R n d l →
      (n : ℝ) * d / 20 ≤ ((privEdges H R).card : ℝ) →
      Eq5 d l r →
      ∃ Q : Finset (Sym2 V), Q ⊆ R ∧ ∃ S : Finset V, Covers H S Q ∧
        c₀ * d ^ 2 * Real.sqrt r ≤ (Q.card : ℝ) ∧
        (S.card : ℝ) ≤ c₁ * (Q.card : ℝ) / d ∧
        DiamLE H S (c₂ * r) := by sorry

end DistancePreserver934.Exact
