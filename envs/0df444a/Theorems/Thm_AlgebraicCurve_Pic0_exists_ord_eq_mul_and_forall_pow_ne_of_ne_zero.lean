-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero
-- name    : AlgebraicCurve.Pic0.exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/72f14308-7737-5d4c-bf0d-dc3be71017a1
-- title:
--   Kummer witness for a nonzero n-torsion divisor class
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $n$ be a natural number with $n \neq 0$. A place of $F$ over $K$ is, by definition, a valuation subring of $F$ containing $\mathrm{image}(K \to F)$, different from $F$ itself, and a principal ideal ring; each such place $v$ has an order function $\mathrm{ord}_v \colon F \to \mathbb{Z}$ coming from the associated height-one adic valuation. Divisors are the finitely supported functions from places to $\mathbb{Z}$, $\mathrm{degZero}$ is the kernel of the degree homomorphism $D \mapsto \sum_v D(v)\deg(v)$, the principal divisors are those of the form $v \mapsto \mathrm{ord}_v(f)$ for some $f \neq 0$, and $\mathrm{Pic}^0$ is the quotient of $\mathrm{degZero}$ by the principal divisors of degree zero. Let $x \in \mathrm{Pic}^0$ satisfy $(n : \mathbb{Z}) \cdot x = 0$ and $x \neq 0$. The assertion is that there exist a degree-zero divisor $D$ and an element $f \in F$ such that the class of $D$ is $x$, $f \neq 0$, $\mathrm{ord}_v(f) = n \, D(v)$ for every place $v$, and $b^{n} \neq f$ for every $b \in F$. The last clause asserts only that $f$ is not an $n$-th power in $F$, not the stronger statement that $f$ is not a constant multiple of an $n$-th power.
--
--   This is the standard Kummer-theoretic description of the $n$-torsion of the degree-zero divisor class group of a function field, in the form in which a nonzero torsion class produces a function whose divisor is $n$ times a divisor and which is itself not an $n$-th power. It is used to prove injectivity of the homomorphism attached to the divisorial Weil pairing data, in the divisible and in the coprime algebraically closed settings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) (hx0 : x ≠ 0) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (f : F),
      Pic0.mk D = x ∧ f ≠ 0 ∧ (∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) ∧
        ∀ b : F, b ^ n ≠ f := by sorry
