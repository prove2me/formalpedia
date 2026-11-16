-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_corollary_29
-- name    : DistancePreserver934.Exact.Supplement.corollary_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:24:41.774355+00:00
-- url     : https://prove2.me/theorems/c72a00fd-cc48-4ab4-ab01-323a0d2653e1
-- title:
--   Corollary 29 — Assigned essential labels extract a large batch with a small hitting set
-- statement:
--   Let $H$ be a minimal preserver of $(G,R)$ retaining all $n$ vertices, with technical unordered demands, and put $d_H=|E(H)|/n$. If real $6\le r\le d_H^2$ and every full demand distance in $H$ is at least $r$, there are nonempty $Q\subseteq R$ and $S\subseteq V$ such that $S$ hits $Q$ and
--
--   $$|Q|\ge c d_H^2\sqrt r,\qquad |S|\le A|Q|/d_H^2,\qquad\operatorname{diam}_H(S)\le8r,$$
--
--   where $c,A>0$ are joint absolute constants. No private-edge or private-length hypothesis is imposed. Essentiality and geometry refer to current $H$. At $n=0$ the density is zero and the radius interval is impossible. This is the assigned-label extraction used for additive spanners.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: absolute O and Ω coefficients → positive existential real coefficients before every graph, demand and real parameter; reason: this makes the source uniformity explicit without selecting unsupported numerical constants
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Corollary 29, printed p. 27 (PDF p. 28)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem corollary_29 :

  ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ {V : Type} [Fintype V]
    (G H : SimpleGraph V) (R : Finset (Sym2 V)) (r : ℝ),
    let dH := (numEdges H : ℝ) / (Fintype.card V : ℝ)
    IsDemandSet G R → IsMinimalPreserver G H R → 6 ≤ r → r ≤ dH ^ 2 →
    (∀ s t : V, s(s, t) ∈ R → ∃ l : ℕ, H.edist s t = (l : ℕ∞) ∧ r ≤ (l : ℝ)) →
    ∃ (Q : Finset (Sym2 V)) (S : Finset V),
      Q.Nonempty ∧ S.Nonempty ∧ Q ⊆ R ∧ HitsAll H S Q ∧
      c * dH ^ 2 * Real.sqrt r ≤ (Q.card : ℝ) ∧
      (S.card : ℝ) ≤ A * (Q.card : ℝ) / dH ^ 2 ∧ DiamLE H S (8 * r)
 := by sorry

end DistancePreserver934.Exact.Supplement
