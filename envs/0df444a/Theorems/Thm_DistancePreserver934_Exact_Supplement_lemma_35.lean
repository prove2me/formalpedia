-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_lemma_35
-- name    : DistancePreserver934.Exact.Supplement.lemma_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:27:43.112066+00:00
-- url     : https://prove2.me/theorems/71ce4e2d-5bf8-4ab7-82e0-a1dd6687545a
-- title:
--   Lemma 35 — Completion of a constant fraction without a logarithmic loss
-- statement:
--   Fix an exponent $\eta>0$ and a uniform half-cover cost coefficient $B>0$. There is $C_{\eta,B}>0$, independent of $n$, graph, source set, demand count, scale and error, with the following property. In a fixed graph $G$, fix an integer error $\beta$, a nonnegative scale $a=A(n,\sigma)$, and a predicate on demand sets closed under taking subsets. For every admissible residual $R$ of size $q>\sqrt n$, assume
--
--   $$a q^\eta\ge n,\qquad\exists J_R\subseteq G:\ J_R\text{ satisfies at least half of }R\text{ with error }\beta,\quad |E(J_R)|\le B a q^\eta.$$
--
--   Then every admissible original set $P$ of size $p$ has a full additive $+\beta$ spanner with
--
--   $$|E(J)|\le C_{\eta,B}(n+a p^\eta).$$
--
--   The fixed source restriction, if present, is part of the downward-closed predicate. The scale is fixed while residual demand sets change. The conclusion is not included in the half-cover premise. This is the shared completion tool for Theorems 36 and 37.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: fixed scale A(n,σ), subset-persistent construction hypotheses and uniform O(f) cost → a nonnegative fixed real a, a downward-closed demand predicate and one coefficient B; completion coefficient chosen before all instance data; reason: for fixed graph and sources only A(n,σ) is used; the premise quantifies over every admissible residual and retains the cutoff sqrt(n)
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Lemma 35, printed p. 32 (PDF p. 33)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem lemma_35 :

  ∀ η B : ℝ, 0 < η → 0 < B → ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (β : ℕ)
      (a : ℝ) (Admissible : Finset (V × V) → Prop),
    0 ≤ a →
    (∀ R Q : Finset (V × V), Q ⊆ R → Admissible R → Admissible Q) →
    (∀ R : Finset (V × V), Admissible R →
      Real.sqrt (Fintype.card V : ℝ) < (R.card : ℝ) →
      (Fintype.card V : ℝ) ≤ a * (R.card : ℝ) ^ η ∧
      ∃ J : SimpleGraph V, HalfSatisfied G J R β ∧
        (numEdges J : ℝ) ≤ B * a * (R.card : ℝ) ^ η) →
    ∀ P : Finset (V × V), Admissible P →
    ∃ J : SimpleGraph V, IsAdditive G J P β ∧
      (numEdges J : ℝ) ≤ C * ((Fintype.card V : ℝ) + a * (P.card : ℝ) ^ η)
 := by sorry

end DistancePreserver934.Exact.Supplement
