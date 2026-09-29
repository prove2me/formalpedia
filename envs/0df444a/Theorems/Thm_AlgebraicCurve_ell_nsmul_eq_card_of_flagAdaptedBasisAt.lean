-- Prove2me | Theorems.Thm_AlgebraicCurve_ell_nsmul_eq_card_of_flagAdaptedBasisAt
-- name    : AlgebraicCurve.ell_nsmul_eq_card_of_flagAdaptedBasisAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/dd7544f5-8d8d-5c62-a6e3-c2c78c4b779f
-- title:
--   Dimension of L(mD) via an adapted monomial family
-- statement:
--   Let $K \subseteq F$ be fields, let $x \in F$ and let $D$ be a divisor on $F$ over $K$, i.e. a finitely supported integer-valued function on the places of $K$ in $F$ (valuation subrings of $F$ containing the image of $K$, proper, with principal ideals), and assume $D v = \max(0, -\operatorname{ord}_v x)$ at every place $v$, where $\operatorname{ord}_v$ is minus the logarithm of the $v$-adic valuation. Let $y_\sigma \in F$ and $e_\sigma \in \mathbb{N}$ be given for $\sigma$ in $\mathrm{Fin}\,d'$, with $y_\sigma$ lying in the Riemann–Roch space $L(e_\sigma \cdot D) = \{f : v(f) \le \exp(e_\sigma D v)$ for all $v\}$. Let $m \in \mathbb{N}$ be such that $L(m\cdot D)$ is finite-dimensional over $K$, such that $L(m \cdot D)$ is contained in the $K$-span of $\{x^j y_\sigma : j + e_\sigma \le m\}$, and such that the finite family of products $x^j y_\sigma$, indexed by the pairs $(\sigma, j)$ with $j + e_\sigma \le m$, is $K$-linearly independent. Then $\ell(m \cdot D) = \dim_K L(m\cdot D) = \sum_{\sigma,\ e_\sigma \le m} (m + 1 - e_\sigma)$, the summands being computed in $\mathbb{N}$.
--
--   This is the dimension count attached to a family of monomials $x^j y_\sigma$ adapted to the pole filtration of the divisor $D$ of poles of $x$: spanning at level $m$ together with linear independence of the level-$m$ monomials pins down $\ell(m\cdot D)$ exactly. It is used in the construction of regular prolongations, in [`AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_forall_ell_nsmul_le`](thm.html#AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_forall_ell_nsmul_le), to bound the growth of $\ell(m\cdot D)$ in $m$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ell_nsmul_eq_card_of_flagAdaptedBasisAt.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.ell_nsmul_eq_card_of_flagAdaptedBasisAt
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    {d' : ℕ} (y : Fin d' → F) (e : Fin d' → ℕ)
    (hyL : ∀ σ, y σ ∈ LSpace ((e σ) • D))
    (m : ℕ) [FiniteDimensional K ↥(LSpace (m • D))]
    (hspan : (LSpace (m • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ m ∧ z = x ^ j * y σ})
    (hLI : LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ m} => x ^ p.val.2 * y p.val.1)) :
    ell (m • D)
      = ∑ σ ∈ (Finset.univ : Finset (Fin d')).filter (fun σ => e σ ≤ m), (m + 1 - e σ) := by sorry
