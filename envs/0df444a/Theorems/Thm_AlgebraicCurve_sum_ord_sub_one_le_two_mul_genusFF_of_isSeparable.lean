-- Prove2me | Theorems.Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable
-- name    : AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/c3b8311a-5293-58eb-8c4d-de3f0a048029
-- title:
--   Hurwitz ramification bound for a separable function field over the line
-- statement:
--   Let $k$ be an algebraically closed field (no restriction on the characteristic) and let $F$ be a field extension of $k$. Let $x \in F$ be transcendental over $k$, and assume that $F$ is finite-dimensional and separable over the intermediate field $k(x) =$ `IntermediateField.adjoin k {x}`. Places of $F/k$ are, as in this development, valuation subrings of $F$ that contain the image of $k$, are proper, and are principal ideal rings; for such a place $P$ and $f \in F$, $P.\mathrm{ord}(f)$ is minus the logarithm of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to $P$. Let $T$ be a finite set of places together with a function $a$ assigning to each place an element $a_P \in k$, such that $\mathrm{ord}_P(x - a_P) > 0$ for every $P \in T$, and let $T_\infty$ be a finite set of places with $\mathrm{ord}_P(x) < 0$ for every $P \in T_\infty$ (so $T$ and $T_\infty$ are automatically disjoint). Then
--   $$\sum_{P \in T}\bigl(\mathrm{ord}_P(x-a_P)-1\bigr)+\sum_{P\in T_\infty}\bigl(-\mathrm{ord}_P(x)-1\bigr)\ \le\ 2\,\mathrm{genusFF}(k,F)-2+2\,[F:k(x)],$$
--   where $\mathrm{genusFF}(k,F)$ is the $k$-dimension of $H^1$ of the zero divisor of $F/k$.
--
--   This is the Riemann–Hurwitz inequality for the extension $F/k(x)$ combined with Dedekind's different inequality $d(P\mid p)\ge e(P\mid p)-1$, packaged as a bound over an arbitrary finite family of places lying over points $x=a_P$ of the affine line and over poles of $x$, so that no enumeration of all ramified places is needed. It is used in the genus estimates for modular curves, for instance in [`ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF`](thm.html#ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF) and in the comparisons of `genusFF` for the various modular function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (a : Place k F → k)
    (hT : ∀ P ∈ T, 0 < P.ord (x - algebraMap k F (a P)))
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, (P.ord (x - algebraMap k F (a P)) - 1) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by sorry
