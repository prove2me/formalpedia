-- Prove2me | Theorems.Thm_CosDensity_Supplement_theorem_4_1
-- name    : CosDensity.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:17:59.618005+00:00
-- url     : https://prove2.me/theorems/baecd903-011e-4121-a8eb-ddbf40208957
-- title:
--   Theorem 4.1 — first density moment identity and exact $d$-word algorithm
-- statement:
--   For every finite stream $P=(x_1,\ldots,x_n)$ in $\mathbb R^d$, write $u_i=x_i/\lVert x_i\rVert_2$ and $s_n=\sum_i u_i$. Then
--   $$M_1(P)=\sum_i\sum_j\langle u_i,u_j\rangle=\lVert s_n\rVert_2^2.$$
--
--   Consequently there is a one-pass algorithm that stores the $d$ coordinates of $s_n$ and outputs $M_1(P)$ exactly, using at most $d$ real words.
--
--   Differences from the source:
--   - generalization: input vectors are nonzero by the paper's standing convention → the identity and algorithm also cover zero vectors using the published convention $\operatorname{unitize}(0)=0$; reason: the bilinear identity remains valid and specializes to every source stream
--   - encoding: $O(d)$ words → a state embedding into exactly $d$ real words; reason: the proof stores only the $d$-coordinate vector sum
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 4.1, p.13 (PDF p.14)

import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_Supplement_WordStreamAlg

open scoped BigOperators RealInnerProductSpace

namespace CosDensity.Supplement

set_option autoImplicit false

/-- Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*,
arXiv:2609.06925 (held version, sha256 f4d4df22…), Theorem 4.1, p.13 (PDF p.14).

The first density moment is the squared norm of the sum of the normalized stream vectors, and a
one-pass algorithm computes it exactly while storing only that `d`-coordinate sum.

**Formalization Note.** The identity and algorithm are stated for all lists, including lists containing
zero vectors; `unitize 0 = 0`, so this is a genuine generalization of the paper's nonzero-input convention.
The algorithm's state embeds into exactly `d` real words. -/
theorem theorem_4_1 :
    (∀ (d : ℕ) (P : List (EuclideanSpace ℝ (Fin d))),
      CosDensity.moment 1 P =
        ‖∑ i : Fin P.length, CosDensity.unitize (P.get i)‖ ^ 2) ∧
    (∀ d : ℕ, ∃ A : WordStreamAlg (EuclideanSpace ℝ (Fin d)),
      A.words ≤ d ∧ ∀ (P : List (EuclideanSpace ℝ (Fin d))) (omega : A.Seed),
        A.estimate omega P = some (CosDensity.moment 1 P)) := by sorry

end CosDensity.Supplement
