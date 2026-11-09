-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_proposition_5_18
-- name    : DetSupportRank.DeterminantSupport.proposition_5_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:54.651932+00:00
-- url     : https://prove2.me/theorems/b37245b6-f4bc-4b87-8978-59172c75b032
-- title:
--   Proposition 5.18 — Initial submodules preserve graded dimensions
-- statement:
--   Let $S=F[x_1,\ldots,x_m]$ have first variable degrees $p_j\in\mathbb N^d\setminus\{0\}$ and second degrees $q_j\in\mathbb N^d$. Let the finite free module have basis bidegrees $(s_i,t_i)\in\mathbb N^d\times\mathbb N^d$. Let $N$ be a submodule graded only in the first degree, and let $N^\sharp=\operatorname{in}(N)$ be its lexicographic second-degree initial module. For every $u\in\mathbb N^d$,
--   $$\dim_F N_u=\dim_F(N^\sharp)_u.$$
--   The positive first weights ensure that the displayed dimensions are finite; second-degree compatibility of $N$ is not an assumption.
--
--   Differences from the source:
--   - encoding: finite coordinate sets [n] and finite tuples → zero-based Fin n, finite subsets, and functions on finite index sets; reason: the index sets are related by a bijection; every source instance is retained
--   - encoding: finite-dimensional component dimensions → Module.finrank of actual intersection subspaces; reason: positivity and finite basis shifts make the first-degree ambient piece finite dimensional, hence also both subspaces
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Proposition 5.18, p. 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_InitialModules

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Krishnan–Moshkovitz, STOC 2027 submission #631, Proposition 5.18, p.23. -/
theorem proposition_5_18 {K : Type*} [Field K] {m d k : ℕ}
    (p q : Fin m → Fin d → ℕ) (hp : ∀ j, p j ≠ 0)
    (s t : Fin k → Fin d → ℕ)
    (N : Submodule (MvPolynomial (Fin m) K) (Fin k → MvPolynomial (Fin m) K))
    (hN : IsGradedSubmodule (fun j i => (p j i : ℤ))
      (fun j i => (s j i : ℤ)) N) (u : Fin d → ℕ) :
    Module.finrank K (submodulePiece (fun j i => (p j i : ℤ))
      (fun j i => (s j i : ℤ)) N (fun i => (u i : ℤ))) =
    Module.finrank K (submodulePiece (fun j i => (p j i : ℤ))
      (fun j i => (s j i : ℤ))
      (initialModule (fun j i => (p j i : ℤ)) (fun j i => (q j i : ℤ))
        (fun j i => (s j i : ℤ)) (fun j i => (t j i : ℤ)) N)
      (fun i => (u i : ℤ))) := by sorry

end DetSupportRank.DeterminantSupport
