-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_Supplement_proposition_4_11
-- name    : DetSupportRank.DeterminantSupport.Supplement.proposition_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:08:56.977198+00:00
-- url     : https://prove2.me/theorems/e314b8a5-0fdb-481d-a482-b2f461e593f9
-- title:
--   Proposition 4.11 — Exact elementary multisymmetric partition rank in characteristic two
-- statement:
--   Let $F$ be any field of characteristic two, including infinite fields, and let $n\ge d\ge3$. For the formal elementary multisymmetric polynomial on $d$ independent $n$-variable row parts,
--   $$\operatorname{PR}(E_{d,n})=\begin{cases}d&d\text{ odd},\\d-1&d\text{ even}.\end{cases}$$
--   This is the exact rank statement supporting the multisymmetric clause of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: one-based indices in [n] → zero-based indices Fin n; reason: the increasing bijection preserves rows, columns and complements; paper i becomes r.val+1, also in signs
--   - encoding: integer minimum partition-decomposition length → the published partitionRank valued in ℕ∞; reason: it is the infimum of actual decomposition lengths and is finite and attained on the source domain; there is no changed rank notion
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Proposition 4.11, p. 13 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_PartitionRank
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_ElementaryMultisymmetric

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Proposition 4.11, p.13; infinite fields of characteristic two are included. -/
theorem proposition_4_11 {F : Type*} [Field F] [CharP F 2]
    (n d : ℕ) (hnd : d ≤ n) (hd : 3 ≤ d) :
    partitionRank (elementaryMultisymmetric F d n) =
      if Odd d then (d : ℕ∞) else ((d - 1 : ℕ) : ℕ∞) := by sorry

end DetSupportRank.DeterminantSupport.Supplement
