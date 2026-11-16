-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_Supplement_theorem_4_3
-- name    : DetSupportRank.DeterminantSupport.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:12:00.04101+00:00
-- url     : https://prove2.me/theorems/43b84564-f3ae-44e9-a0b1-25756d1c6be3
-- title:
--   Theorem 4.3 — Both explicit n−1-product determinant identities (4) and (5)
-- statement:
--   Let $F$ be any field and let $n\ge3$ be even, with $m=n/2$. Put $S_i=\{1,i\}$ and take all minors in increasing row and column order. Both identities hold in the formal polynomial ring:
--   $$\det_n(X)=\sum_{i=2}^n(-1)^i\left(\sum_{|I|=2}\det(X_{S_i,I})\right)\left(\sum_{|J|=n-2}\det(X_{S_i^c,J})\right),$$
--   $$\det_n(X)=\sum_{i=2}^n(-1)^i\left(\sum_{k=1}^m\det(X_{S_i,\{2k-1,2k\}})\right)\left(\sum_{k=1}^m\det(X_{S_i^c,\{2k-1,2k\}^c})\right).$$
--   In each product the two sums are independent. Complements are in the full $[n]$. These are the two explicit determinant decompositions (4) and (5), not merely a rank upper bound.
--
--   Differences from the source:
--   - encoding: one-based indices in [n] → zero-based indices Fin n; reason: the increasing bijection preserves rows, columns and complements; paper i becomes r.val+1, also in signs
--   - encoding: determinants of equal-size ordered row and column subsets → ordered minors with a zero extension at unequal sizes; reason: all uses have equal sizes by their index sets and the source size assumptions; the undefined extension is never used
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Theorem 4.3, p. 10 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_PolynomialMatrices
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_SpecialMatrices

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Theorem 4.3, p.10: BOTH products of independently indexed sums, formulas (4) and (5).
The paper's one-based i becomes r.val+1, including in the sign. -/
theorem theorem_4_3 {F : Type*} [Field F] (n : ℕ) (hn : 3 ≤ n) (he : Even n) :
    (determinantPolynomial F n =
      ∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val ≠ 0),
        MvPolynomial.C ((-1 : F) ^ (r.val + 1)) *
          sumColumnMinors (firstRowPair r) 2 *
          sumColumnMinors (Finset.univ \ firstRowPair r) (n - 2)) ∧
    (determinantPolynomial F n =
      ∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val ≠ 0),
        MvPolynomial.C ((-1 : F) ^ (r.val + 1)) *
          (∑ b : Fin (n / 2), variableMinor (firstRowPair r) (adjacentBlock b)) *
          (∑ b : Fin (n / 2),
            variableMinor (Finset.univ \ firstRowPair r) (Finset.univ \ adjacentBlock b))) := by sorry

end DetSupportRank.DeterminantSupport.Supplement
