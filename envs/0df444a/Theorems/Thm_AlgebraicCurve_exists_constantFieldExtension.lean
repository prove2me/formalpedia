-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension
-- name    : AlgebraicCurve.exists_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/184b88c8-9f1e-5ffd-979c-e9e9b77d5dec
-- title:
--   Existence of the constant field extension F₀K'
-- statement:
--   Let $K_0$, $F_0$, $K'$ be fields with $K_0$-algebra structures on $F_0$ and on $K'$, with $K_0$ algebraically closed of characteristic $0$ and $K'$ algebraically closed. Assume $F_0$ is a function field in one variable over $K_0$ in the form stated: there is $x \in F_0$ transcendental over $K_0$ such that $F_0$ is finite-dimensional over the intermediate field $K_0(x)$. Assume further that $F_0$ is a curve over $K_0$ — i.e. every nonzero $f \in F_0$ has a divisor, a finitely supported integer-valued function on the places of $F_0/K_0$ (valuation subrings of $F_0$ containing the image of $K_0$, distinct from $F_0$ and with principal ideals) whose value at each place $v$ is $\operatorname{ord}_v(f)$ and whose degree is $0$; each place has residue field finite over $K_0$; and $\Omega_{F_0/K_0}$ is free of rank $1$ over $F_0$ — and that $F_0/K_0$ has canonical divisors, i.e. every nonzero $\omega \in \Omega_{F_0/K_0}$ admits a divisor whose value at $v$ is $\operatorname{ord}_v$ of the differential coefficient of $\omega$ at $v$. The conclusion asserts the existence of a field $F'$, in the maximum of the universes of $F_0$ and $K'$, equipped with $K'$-, $F_0$- and $K_0$-algebra structures making $K_0 \to K' \to F'$ and $K_0 \to F_0 \to F'$ towers, such that $F'$ is a curve over $K'$ in the same sense, has canonical divisors over $K'$, contains some $x'$ transcendental over $K'$ with $F'$ finite over $K'(x')$, and is generated as an intermediate field by $K'$ together with the image of $F_0$.
--
--   This is the constant field extension $F' = K'(F_0)$ of a one-variable function field along an extension of algebraically closed fields of characteristic $0$: classically $F_0 \otimes_{K_0} K'$ is a domain whose fraction field is again a function field in one variable, of the same genus. It is used to transfer statements about the torsion of $\mathrm{Pic}^0$ of a curve over an arbitrary algebraically closed field of characteristic $0$ to the case $K' = \mathbb{C}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u v w

theorem AlgebraicCurve.exists_constantFieldExtension (K₀ : Type u) (F₀ : Type v) (K' : Type w)
    [Field K₀] [Field F₀] [Field K'] [Algebra K₀ F₀] [Algebra K₀ K']
    [IsAlgClosed K₀] [CharZero K₀] [IsAlgClosed K']
    (hfg₀ : ∃ x : F₀, Transcendental K₀ x ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀)
    [IsCurveOver K₀ F₀] [HasCanonicalDivisor (K := K₀) (F := F₀)] :
    ∃ (F' : Type (max v w)) (_ : Field F') (_ : Algebra K' F') (_ : Algebra F₀ F')
      (_ : Algebra K₀ F') (_ : IsScalarTower K₀ K' F') (_ : IsScalarTower K₀ F₀ F')
      (_ : IsCurveOver K' F') (_ : HasCanonicalDivisor (K := K') (F := F')),
      (∃ x : F', Transcendental K' x ∧
        FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F') ∧
      IntermediateField.adjoin K' (Set.range (algebraMap F₀ F')) = ⊤ := by sorry
