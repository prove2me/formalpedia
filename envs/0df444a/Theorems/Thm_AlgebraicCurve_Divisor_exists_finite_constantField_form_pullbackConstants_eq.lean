-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_finite_constantField_form_pullbackConstants_eq
-- name    : AlgebraicCurve.Divisor.exists_finite_constantField_form_pullbackConstants_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/ca319e15-c95e-552e-847d-dcfa5168d47c
-- title:
--   Every divisor descends to a finite constant field
-- statement:
--   Let $K'$ be a field of characteristic $\ell$, $\ell$ a prime, and $F'$ a field extension of $K'$. Assume every $a \in K'$ satisfies $a^{\ell^{n}} = a$ for some $n > 0$; that there is some $x \in F'$ transcendental over $K'$ with $F'$ finite-dimensional over $K'(x)$; that $F'/K'$ satisfies `IsCurveOver`, i.e. every nonzero $f \in F'$ has a divisor of degree $0$ recording its orders $\mathrm{ord}_v(f)$ at all places, every place of $F'/K'$ has residue field finite over $K'$, and $\Omega_{F'/K'}$ is free of rank $1$ over $F'$; and that $\mathrm{ConstantsAreBase}$ holds for $K' \subseteq F'$, i.e. the Riemann–Roch space of the zero divisor is exactly the image of $K'$ in $F'$. Here a place is a valuation subring of $F'$ containing the image of $K'$, distinct from $F'$ itself, whose ring is a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places, of degree $\sum_v D(v)\,\deg v$. Then for every divisor $c$ of $F'/K'$ there exist a finite field $K$ and a field $F$, with algebra structures $K \to K'$, $K \to F$, $F \to F'$, $K \to F'$ making $K \subseteq K' \subseteq F'$ and $K \subseteq F \subseteq F'$ towers, with $F'$ integral over $F$, with $F'/F$ satisfying `IsCurveOver` and essentially of finite type over $K$, and a divisor $D$ of $F/K$, such that $F'$ is generated over $F$ by the image of $K'$, $\mathrm{ConstantsAreBase}$ holds for $K \subseteq F$, the constant-field pullback of $D$ equals $c$, and $\deg D = \deg c$.
--
--   This is the descent of a divisor to a finite constant field: a divisor of a function field whose constant field is algebraic over $\mathbb{F}_\ell$ is already defined over a suitable finite subfield, with the same degree. It is the step feeding the results that $\mathrm{Pic}^0$ of such a function field is torsion and that its $\ell'$-torsion has the expected order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_finite_constantField_form_pullbackConstants_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u v

theorem AlgebraicCurve.Divisor.exists_finite_constantField_form_pullbackConstants_eq
    (K' : Type u) (F' : Type v) [Field K'] [Field F'] [Algebra K' F']
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP K' ℓ]
    (halg : ∀ a : K', ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a)
    (hfg : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K' F'] (hC : ConstantsAreBase K' F') (c : Divisor K' F') :
    ∃ (K : Type u) (F : Type v) (_ : Field K) (_ : Finite K) (_ : Field F)
      (_ : Algebra K K') (_ : Algebra K F) (_ : Algebra F F') (_ : Algebra K F')
      (_ : IsScalarTower K K' F') (_ : IsScalarTower K F F') (_ : Algebra.IsIntegral F F')
      (_ : IsCurveOver K F) (_ : Algebra.EssFiniteType K F)
      (D : Divisor K F),
        Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤ ∧
        ConstantsAreBase K F ∧
        Divisor.pullbackConstants K' F' D = c ∧ Divisor.degree D = Divisor.degree c := by sorry
