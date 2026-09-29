-- Prove2me | Theorems.Thm_CannonFloydParry_exists_freeAbelianBasis_infinite_of_not_abelian
-- name    : CannonFloydParry.exists_freeAbelianBasis_infinite_of_not_abelian
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T13:16:45.457565+00:00
-- url     : https://prove2.me/theorems/b482fd52-3e77-4f73-9e41-df9ab7f174f6
-- title:
--   Theorem 4.8: every non-abelian subgroup of $F$ contains a free abelian subgroup of infinite rank
-- statement:
--   Let $K$ be a subgroup of $\operatorname{Aut}[0,1]$ contained in Thompson's group $F$, and
--   suppose $K$ is not abelian (some two of its elements fail to commute). Then $K$ contains a
--   free abelian subgroup of infinite rank, in the following concrete sense: there is a
--   $\mathbb{Z}$-indexed family $x_m \in K$ such that any two $x_p, x_q$ commute and the family is
--   independent — for every finite list of *distinct* indices $m_1, \dots, m_r$ and integers
--   $n_1, \dots, n_r$, if $x_{m_1}^{n_1} \cdots x_{m_r}^{n_r} = 1$ then every $n_i = 0$.
--
--   This is the source's Theorem 4.8. The conclusion is stated as a family with the two
--   properties of a free abelian basis rather than as an abstract subgroup isomorphic to
--   $\bigoplus_{\mathbb{Z}} \mathbb{Z}$; the two are equivalent, and this form is the one the
--   Brin–Squier mission uses for its Theorem (3.2), whose statement this mirrors.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, Theorem 4.8, p. 232.

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

/-- Theorem 4.8.  Every non-abelian subgroup of `F` contains a free abelian subgroup of
infinite rank: a `ℤ`-indexed family in the subgroup that commutes pairwise and is independent
(a product over distinct indices with integer exponents is `1` only when every exponent is
`0`). -/
theorem exists_freeAbelianBasis_infinite_of_not_abelian (K : Subgroup (UI ≃o UI)) (hK : K ≤ F)
    (hne : ¬ ∀ f ∈ K, ∀ g ∈ K, f * g = g * f) :
    ∃ x : ℤ → UI ≃o UI, (∀ m, x m ∈ K) ∧ (∀ p q : ℤ, x p * x q = x q * x p) ∧
      ∀ (l : List ℤ), l.Nodup → ∀ n : ℤ → ℤ,
        (l.map (fun m => x m ^ n m)).prod = 1 → ∀ m ∈ l, n m = 0 := by
  sorry

end CannonFloydParry
