-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_corollary_30
-- name    : DistancePreserver934.Exact.Supplement.corollary_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:25:23.873025+00:00
-- url     : https://prove2.me/theorems/b980509c-072d-40fa-9e38-46b0f6e7b9e8
-- title:
--   Corollary 30 — An extracted batch has a +2 spanner of cost O(n+|Q|√(nr)/d_H)
-- statement:
--   Fix the universal size coefficient $A>0$ of a Corollary 29 certificate. There is $C_A>0$, independent of every graph, radius, demand set and batch, such that every $Q,S$ with the full hypotheses and hitting certificate of that corollary (including a positive lower batch coefficient $c$) admits $J(Q)\subseteq H$ with additive error $+2$ relative to $G$ and
--
--   $$|E(J(Q))|\le C_A\bigl(n+|Q|\sqrt{nr}/d_H\bigr).$$
--
--   Here $d_H=|E(H)|/n$, $Q,S$ are nonempty, $S$ hits $Q$, $|Q|\ge c d_H^2\sqrt r$, $|S|\le A|Q|/d_H^2$ and $\operatorname{diam}_H(S)\le8r$. The coefficient does not depend on $c$. Thus every certified extraction batch, including those with the fixed universal constants of Corollary 29, is covered. This supplies the saved batch cost for Lemma 31.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - generalization: the batch obtained with the fixed universal extraction coefficients in Corollary 29 → every batch certified by those inequalities for any fixed positive size coefficient A and positive lower coefficient c, with the cost coefficient depending only on A; reason: Lemma 28 uses only the hitting certificate and its upper size and diameter bounds; fixing A to the universal coefficient of Corollary 29 recovers every source instance
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Corollary 30, printed p. 28 (PDF p. 29)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem corollary_30 :

  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V]
    (G H : SimpleGraph V) (R Q : Finset (Sym2 V)) (S : Finset V) (r c : ℝ),
    let n := (Fintype.card V : ℝ)
    let dH := (numEdges H : ℝ) / n
    IsDemandSet G R → IsMinimalPreserver G H R → 6 ≤ r → r ≤ dH ^ 2 →
    (∀ s t : V, s(s, t) ∈ R → ∃ l : ℕ, H.edist s t = (l : ℕ∞) ∧ r ≤ (l : ℝ)) →
    0 < c → Q.Nonempty → S.Nonempty → Q ⊆ R → HitsAll H S Q →
    c * dH ^ 2 * Real.sqrt r ≤ (Q.card : ℝ) →
    (S.card : ℝ) ≤ A * (Q.card : ℝ) / dH ^ 2 → DiamLE H S (8 * r) →
    ∃ J : SimpleGraph V, J ≤ H ∧ IsAdditiveUnordered G J Q 2 ∧
      (numEdges J : ℝ) ≤ C * (n + (Q.card : ℝ) * Real.sqrt (n * r) / dH)
 := by sorry

end DistancePreserver934.Exact.Supplement
