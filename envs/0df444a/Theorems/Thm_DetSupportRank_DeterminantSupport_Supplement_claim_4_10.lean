-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_Supplement_claim_4_10
-- name    : DetSupportRank.DeterminantSupport.Supplement.claim_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:11:20.444214+00:00
-- url     : https://prove2.me/theorems/3f30dd63-43a7-4077-b25b-d868eb86dee1
-- title:
--   Claim 4.10 — Sparse alternating matrix and all its principal Pfaffians
-- statement:
--   Let $F$ be any field and $n\ge0$ even. For the sparse alternating block matrix $L_n$, and every principal index subset $J\subseteq[n]$,
--   $$\operatorname{pf}(L_n)=1,\qquad \operatorname{pf}((L_n)_{J,J})=\begin{cases}1&J\text{ aligned},\\0&J\text{ not aligned}.\end{cases}$$
--   Aligned means a union of whole adjacent two-element blocks; all submatrices inherit increasing order. The empty matrix and empty subset are included. This full dichotomy supplies the sparse-matrix specialization used in formula (5) of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: one-based indices in [n] → zero-based indices Fin n; reason: the increasing bijection preserves rows, columns and complements; paper i becomes r.val+1, also in signs
--   - encoding: signed sum over ordered pair partitions → signed sum over their unique canonical permutations; reason: pairs occupy even-odd consecutive positions, are oriented increasingly and are ordered by first endpoint, exactly as equation (3); no multiplicity or division
--   - encoding: even-order source Pfaffian and all principal subsets → odd-order principal matching sum is zero; reason: there are no perfect matchings of an odd set; this total convention changes no even-order source instance, and retains every subset in the printed dichotomy
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Claim 4.10, p. 12 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_OrderedSubmatrices
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_Pfaffian
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_SpecialMatrices

noncomputable section
open scoped BigOperators
open Classical

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Claim 4.10, p.12: the full principal-submatrix dichotomy, including the empty subset. -/
theorem claim_4_10 {F : Type*} [Field F] (n : ℕ) (he : Even n) :
    pfaffian (sparseL F n) = 1 ∧
      ∀ J : Finset (Fin n),
        pfaffian (orderedSubmatrix (sparseL F n) J J) =
          if IsAligned J then 1 else 0 := by sorry

end DetSupportRank.DeterminantSupport.Supplement
