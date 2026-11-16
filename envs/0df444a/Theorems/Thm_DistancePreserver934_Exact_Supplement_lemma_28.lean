-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_lemma_28
-- name    : DistancePreserver934.Exact.Supplement.lemma_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:24:05.744198+00:00
-- url     : https://prove2.me/theorems/ce5a100d-e6c8-4370-9db1-a6f94c80c712
-- title:
--   Lemma 28 — A hitting set gives a +2 spanner inside the preserver
-- statement:
--   Let $H$ be a minimal preserver of $(G,R)$ on at most $n$ vertices, with normalized distinct reachable unordered demands. Suppose $\varnothing\ne Q\subseteq R$ and nonempty $S$ hits $Q$ in $H$, with finite $D=\operatorname{diam}_H(S)$. For one absolute $C>0$, there is $J\subseteq H$ with additive error $+2$ on $Q$ relative to $G$, and
--
--   $$|E(J)|\le C\bigl(n+\sqrt{n|Q||S|D}\bigr).$$
--
--   The guarantee includes both distance inequalities, retains containment in $H$, and allows $D=0$, including a singleton hitting set. This converts a hitting certificate into an additive batch spanner.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: absolute O and Ω coefficients → positive existential real coefficients before every graph, demand and real parameter; reason: this makes the source uniformity explicit without selecting unsupported numerical constants
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Lemma 28, printed p. 26–27 (PDF p. 27–28)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem lemma_28 :

  ∃ C : ℝ, 0 < C ∧ ∀ {V : Type} [Fintype V]
    (G H : SimpleGraph V) (R Q : Finset (Sym2 V)) (S : Finset V) (n : ℕ),
    Fintype.card V ≤ n → IsDemandSet G R → IsMinimalPreserver G H R →
    Q.Nonempty → Q ⊆ R → S.Nonempty → HitsAll H S Q → diam H S ≠ ⊤ →
    ∃ J : SimpleGraph V, J ≤ H ∧ IsAdditiveUnordered G J Q 2 ∧
      (numEdges J : ℝ) ≤ C * ((n : ℝ) +
        Real.sqrt ((n : ℝ) * (Q.card : ℝ) * (S.card : ℝ) * ((diam H S).toNat : ℝ)))
 := by sorry

end DistancePreserver934.Exact.Supplement
