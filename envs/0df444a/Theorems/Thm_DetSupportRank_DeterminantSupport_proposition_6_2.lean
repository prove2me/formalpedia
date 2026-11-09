-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_proposition_6_2
-- name    : DetSupportRank.DeterminantSupport.proposition_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:40.049355+00:00
-- url     : https://prove2.me/theorems/75b38266-1ebf-4d62-bfa8-a60946e60e87
-- title:
--   Proposition 6.2 — The complex root orbit lies in the degree variety
-- statement:
--   Let $F$ be any field, let $n\ge2$, and let $D$ have determinant support. For $\zeta=e^{2\pi i/n}$ and $\boldsymbol\zeta=(1,\zeta,\ldots,\zeta^{n-1})$,
--   $$\{\boldsymbol\zeta^\sigma:\sigma\in S_n\}\subseteq X_{n-1}(D).$$
--   The root vector is constructed in $\mathbb C$ independently of $F$. The statement includes every permutation and every independent nonzero coefficient choice.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: independent nonzero field coefficients cσ → a function from permutations to field units; reason: every nonzero field element determines a unique unit, so this parametrizes exactly the source family
--   - generalization: the main-theorem working context n≥3 in §6 → all n≥2; reason: the proof via the roots of t^n−1 and Theorem 5.1 works for every n≥2, where n−1 is a positive variety index
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Proposition 6.2, p. 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Permutations

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Proposition 6.2, p.27. -/
theorem proposition_6_2 {K : Type*} [Field K] {n : ℕ}
    (hn : 2 ≤ n) (c : Equiv.Perm (Fin n) → Kˣ) :
    ∀ σ : Equiv.Perm (Fin n),
      (fun i => rootVector n (σ i)) ∈ degreeVariety (determinantSupportPolynomial c) (n - 1) := by sorry

end DetSupportRank.DeterminantSupport
