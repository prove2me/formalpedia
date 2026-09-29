-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_forall_pow_eq_self
-- name    : AlgebraicCurve.Pic0.natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_forall_pow_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/2722703e-d2a0-5554-8327-9350b3196bae
-- title:
--   Order of the ℓ^k-torsion of Pic⁰
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure. Assume $K$ has characteristic a prime $p$ and that every $a \in K$ satisfies $a^{p^n} = a$ for some $n > 0$. Assume further that $F$ is a curve over $K$ in the sense of the predicate `IsCurveOver`: every nonzero $f \in F$ admits a divisor recording its orders $\mathrm{ord}_v(f)$ at all places $v$ (places being valuation subrings of $F$ containing the image of $K$, distinct from $F$ itself, whose rings are principal ideal rings) and of total degree $0$; each place has residue field of finite dimension over $K$; and $\Omega_{F/K}$ is free of rank $1$ over $F$. Assume also that $F$ is essentially of finite type over $K$. Let $\ell$ be a prime whose image in $K$ is nonzero, and let $k \in \mathbb{N}$. Then the group of $\ell^k$-torsion elements of $\mathrm{Pic}^0(F/K)$ — the quotient of the degree-zero divisors by the principal ones, with torsion taken in the sense of $\mathbb{Z}$-module torsion by $\ell^k$ — is finite of cardinality $\ell^{2 g k}$, where $g = \mathrm{genusFF}(K,F)$ is the $K$-dimension of $H^1$ of the zero divisor.
--
--   This is the classical computation $\#J[\ell^k] = \ell^{2gk}$ for the Jacobian of a curve of genus $g$ over an algebraically closed field of characteristic $p$ algebraic over $\mathbb{F}_p$, with $\ell \neq p$, here formulated for the divisor class group $\mathrm{Pic}^0(F/K)$ of a function field. It feeds the torsion estimates used in the analysis of nodal reductions and of semistable models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_forall_pow_eq_self.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.natCard_torsion_pow_eq_pow_two_mul_genusFF_mul_of_forall_pow_eq_self
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) (k : ℕ) :
    Nat.card (Pic0.torsion K F (ℓ ^ k)) = ℓ ^ (2 * genusFF K F * k) := by sorry
