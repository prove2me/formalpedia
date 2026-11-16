-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_Supplement_theorem_4_8
-- name    : DetSupportRank.DeterminantSupport.Supplement.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:12:26.657884+00:00
-- url     : https://prove2.me/theorems/e817731f-0449-4ec1-b897-10e821351ddf
-- title:
--   Theorem 4.8 — General normalized Pfaffian determinant expansion with valid row partitions
-- statement:
--   Let $F$ be any field, $n\ge3$ even, and $K$ any alternating scalar $n\times n$ matrix such that $\operatorname{pf}(K)=1$. Put $M=XKX^{\mathsf T}$ and $S_i=\{1,i\}$. Then the formal identity is
--   $$\det_n(X)=\sum_{i=2}^n(-1)^iM_{1,i}\operatorname{pf}(M_{S_i^c,S_i^c}).$$
--   For each displayed term, $S_i$ is a nonempty proper row subset, $M_{1,i}$ is set-multilinear on $S_i$, and its displayed Pfaffian factor is set-multilinear on the complementary rows. Thus this is an actual partition decomposition with $n-1$ terms. No characteristic, invertibility, or assumed-decomposition condition is added. This companion theorem supplies the general family behind the two identities of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: one-based indices in [n] → zero-based indices Fin n; reason: the increasing bijection preserves rows, columns and complements; paper i becomes r.val+1, also in signs
--   - encoding: signed sum over ordered pair partitions → signed sum over their unique canonical permutations; reason: pairs occupy even-odd consecutive positions, are oriented increasingly and are ordered by first endpoint, exactly as equation (3); no multiplicity or division
--   - encoding: the expansion is a valid partition rank decomposition → the identity, the displayed factors’ set-multilinearity on complementary nonempty proper row subsets, and HasPartitionDecomposition with length n−1; reason: spells out every part of validity using the unchanged published predicate; no decomposition fact becomes a hypothesis
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Theorem 4.8, p. 11 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_PartitionRank
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_AlternatingMatrices
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_Pfaffian
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_PolynomialMatrices

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Theorem 4.8, p.11: the actual expansion and validity of its displayed row factors.
No hypothesis asserts the expansion or multilinearity of its factors. -/
theorem theorem_4_8 {F : Type*} [Field F] (n : ℕ) (hn : 3 ≤ n) (he : Even n)
    (K : Matrix (Fin n) (Fin n) F) (hK : IsAlternating K) (hpf : pfaffian K = 1) :
    let M := conjugatedMatrix K
    let first : Fin n := ⟨0, by omega⟩
    (determinantPolynomial F n =
      ∑ r ∈ Finset.univ.filter (fun r : Fin n => r.val ≠ 0),
        MvPolynomial.C ((-1 : F) ^ (r.val + 1)) * M first r *
          pfaffian (orderedSubmatrix M (Finset.univ \ firstRowPair r)
            (Finset.univ \ firstRowPair r))) ∧
    (∀ r : Fin n, r.val ≠ 0 →
      (firstRowPair r).Nonempty ∧ firstRowPair r ≠ Finset.univ ∧
      SetMultCost.IsSetMultilinearOn Prod.fst (firstRowPair r) (M first r) ∧
      SetMultCost.IsSetMultilinearOn Prod.fst (Finset.univ \ firstRowPair r)
        (pfaffian (orderedSubmatrix M (Finset.univ \ firstRowPair r)
          (Finset.univ \ firstRowPair r)))) ∧
    HasPartitionDecomposition (determinantPolynomial F n) (n - 1) := by sorry

end DetSupportRank.DeterminantSupport.Supplement
