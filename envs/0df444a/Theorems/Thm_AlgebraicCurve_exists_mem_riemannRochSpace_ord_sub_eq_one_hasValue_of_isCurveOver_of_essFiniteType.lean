-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType
-- name    : AlgebraicCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/3e351da7-e87a-5c6d-a845-2acb4b854dc0
-- title:
--   Riemann–Roch interpolation: simple zero at one place, prescribed values
-- statement:
--   Let $k$ be an algebraically closed field and $F$ a field equipped with a $k$-algebra structure such that `IsCurveOver k F` holds — that is, every nonzero $f \in F$ has a divisor $D$ on the places of $F/k$ with $D(v) = \operatorname{ord}_v f$ at every place and $\deg D = 0$, every place has residue field finite over $k$, and $\Omega_{F/k}$ is free of rank $1$ over $F$ — and such that $F$ is essentially of finite type over $k$. Let $U$, $Z_v$, $Z_a$ be finite sets of places of $F/k$ that are pairwise disjoint, let $t_0$ be a place belonging to none of the three, let $\beta \in k$, let $\mathrm{val}$ be an arbitrary $k$-valued function on places, and let $\mathrm{bad}$ be a finite subset of $k$. Assume $\#Z_v + 2\,\mathrm{genusFF}\,k\,F + 2 \le \#U$, where `genusFF k F` is the $k$-dimension of $H^1$ of the zero divisor. Then there exists $g \in F$ lying in the Riemann–Roch space of the divisor $\sum_{u \in U} u$, i.e. $v(g) \le \exp(D(v))$ for the adic valuation at every place $v$, so that $g$ has at worst simple poles and only at places of $U$, such that $\operatorname{ord}_{t_0}\!\bigl(g - \beta\bigr) = 1$; such that for each $z \in Z_v$ the element $g$ lies in the valuation ring of $z$ with residue the image of $\mathrm{val}(z)$ in the residue field of $z$; and such that for each $z \in Z_a$ there is some $\gamma \in k$ outside $\mathrm{bad}$ with $g$ in the valuation ring of $z$ and residue the image of $\gamma$.
--
--   This is the standard interpolation consequence of the Riemann–Roch theorem on a curve over an algebraically closed field: for a divisor of large enough degree the prescribed value conditions, together with a first-order condition at one extra place, can be met inside the corresponding Riemann–Roch space, and finitely many forbidden values may be avoided because $k$ is infinite. It is used to produce functions with controlled poles, a simple zero of $g-\beta$ at a chosen place and prescribed or generic values elsewhere, in the construction of semistable coverings and in the specialisation arguments on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_isCurveOver_of_essFiniteType
    (k F : Type*) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (U Zv Za : Finset (Place k F)) (t₀ : Place k F) (β : k)
    (val : Place k F → k) (bad : Finset k)
    (hUZv : Disjoint U Zv) (hUZa : Disjoint U Za) (hZ : Disjoint Zv Za)
    (ht₀U : t₀ ∉ U) (ht₀v : t₀ ∉ Zv) (ht₀a : t₀ ∉ Za)
    (hcard : Zv.card + 2 * genusFF k F + 2 ≤ U.card) :
    ∃ g : F,
      g ∈ riemannRochSpace (∑ u ∈ U, Finsupp.single u (1 : ℤ)) ∧
      t₀.ord (g - algebraMap k F β) = 1 ∧
      (∀ z ∈ Zv, z.HasValue g (val z)) ∧
      (∀ z ∈ Za, ∃ γ : k, γ ∉ bad ∧ z.HasValue g γ) := by sorry
