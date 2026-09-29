-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_exists_baseAut_eq_of_constantFieldExtension
-- name    : AlgebraicCurve.SemilinearAut.exists_baseAut_eq_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/f877cd2d-b2f3-5249-bd34-76d0bb336258
-- title:
--   Extending constant-field automorphisms to F-fixing semilinear automorphisms
-- statement:
--   Let $K$, $F$, $K'$, $F'$ be fields with $F$ a $K$-algebra, $F'$ a $K'$-algebra, $K'$ a $K$-algebra, $F'$ an $F$-algebra and a $K$-algebra, the two towers $K \to K' \to F'$ and $K \to F \to F'$ being compatible, and suppose $K$ is algebraically closed of characteristic $0$. Assume $F$ contains an element $x$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$, that $F'$ contains an element transcendental over $K'$ over whose adjunction to $K'$ the field $F'$ is finite-dimensional, and that the subfield of $F'$ generated over $K'$ by the image of $F$ is all of $F'$. Then for every automorphism $\tau$ of $K'$ as a $K$-algebra there is an element $g$ of `SemilinearAut K' F'`, that is, a pair consisting of a ring automorphism $\sigma$ of $F'$ and a ring automorphism $\rho$ of $K'$ with $\sigma(\mathrm{alg}_{K' \to F'}(a)) = \mathrm{alg}_{K' \to F'}(\rho(a))$ for all $a \in K'$, such that its second component satisfies $\rho(a) = \tau(a)$ for all $a \in K'$, and such that the action of $g$ on $F'$ through $\sigma$ fixes the image of $F$ pointwise: $\sigma(\mathrm{alg}_{F \to F'}(y)) = \mathrm{alg}_{F \to F'}(y)$ for all $y \in F$.
--
--   This is the standard statement that for a constant-field extension $F' = F \cdot K'$ of a function field $F$ in one variable with algebraically closed field of constants $K$, every $K$-automorphism of $K'$ lifts to an automorphism of $F'$ fixing $F$. It is used in the descent of torsion divisor classes along a constant-field extension ([`AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension_of_finite`](thm.html#AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension_of_finite)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_exists_baseAut_eq_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.SemilinearAut.exists_baseAut_eq_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (τ : K' ≃ₐ[K] K') :
    ∃ g : SemilinearAut K' F',
      (∀ a : K', SemilinearAut.baseAut g a = τ a) ∧
      ∀ y : F, g • algebraMap F F' y = algebraMap F F' y := by sorry
