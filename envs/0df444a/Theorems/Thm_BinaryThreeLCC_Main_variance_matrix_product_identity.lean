-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_variance_matrix_product_identity
-- name    : BinaryThreeLCC.Main.variance_matrix_product_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:55.426303+00:00
-- url     : https://prove2.me/theorems/a1eb407e-84a3-48c9-b95e-b1baca23072f
-- title:
--   Claim 5.6 — exact variance and matrix product identity
-- statement:
--   Let $\Omega,\Lambda$ be nonempty finite sets, $m=|\Omega|$, and $\mathcal H$ a distinct-pair tuple system unique at each $(u,a)$. Construct its tuple multiset $\mathcal T$ with the prescribed fake copies and matrices $M_a(u',u)=\tfrac12|\{(u,a,\star,u')\in\mathcal T\}|$. Fix a nonempty palette $\mathcal C\subseteq\Omega$ and $r\ge1$. For the local variance $\mathcal V$ of the ordered chain Kikuchi graph, uniformly averaged over both tagged vertex sides and over the whole palette,
--
--   $$\mathcal V=\frac{2^{2r}}{2(m+1)}\,
--   \mathbb E_{i,i'\in\mathcal C}\mathbb E_{a_1,\ldots,a_r\in\Lambda}
--   \left\|M_{a_r}\cdots M_{a_1}(e_i-e_{i'})\right\|_2^2.$$
--
--   Every coordinate and both colours are chosen independently and uniformly. This is an exact equality; the factor $2^{2r}/(2(m+1))$ and all edge multiplicities are retained.
--
--   Differences from the source:
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - encoding: uniform averages over vertices, colours and coordinates; squared Euclidean norm → nonempty Ω, Λ and palette, finite uniform averages, sum of squared coordinates and reversed matrix product; reason: these express the same distributions, norm and order without degree-weighting vertices
--   - generalization: the surrounding proof also has independent vector labels and an expanding Eulerian flattening → the identity is stated without vector labels, independence, expansion or balance hypotheses; reason: it is a tuple-count identity and all source instances are retained
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Claim 5.6, printed p. 15, PDF p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Kikuchi

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Claim 5.6. Both colour choices and every ordered coordinate are uniform and independent. -/
theorem variance_matrix_product_identity {Ω Λ : Type} [Fintype Ω] [DecidableEq Ω]
    [Fintype Λ] [Nonempty Λ]
    (H : TupleSystem Ω Λ) (C : Finset Ω) (hC : C.Nonempty) (r : ℕ) (hr : 1 ≤ r) :
    localVariance (kikuchiGraph H C r) =
      (2 : ℝ) ^ (2 * r) / (2 * ((Fintype.card Ω : ℝ) + 1)) *
        productDifferenceAverage H C r := by sorry

end BinaryThreeLCC.Main
