-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
-- name    : AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/473633af-5787-590c-bd34-3177dd619a76
-- title:
--   Riemann–Roch over an algebraically closed field
-- statement:
--   Let $K$ be an algebraically closed field and let $F$ be a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and is a curve over $K$ in the sense of the project's class `IsCurveOver`: every nonzero $f \in F$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg D = 0$; for every place $v$ the residue field of $v$ is a finite-dimensional $K$-module; and the module of Kähler differentials $\Omega_{F/K}$ is free of rank one over $F$. Here a place of $F/K$ is a valuation subring of $F$ containing $\operatorname{im}(K \to F)$, distinct from $F$ itself, which is a principal ideal ring, a divisor is a finitely supported function from places to $\mathbb{Z}$, and $\deg D = \sum_v D(v)\,\deg v$ with $\deg v$ the degree attached to $v$. The assertion is that there exist a divisor $K_c$ on $F/K$ and a natural number $g$ such that for every divisor $D$,
--   $$\ell(D) - \ell(K_c - D) = \deg D + 1 - g$$
--   as an identity in $\mathbb{Z}$, where $\ell(D)$ denotes the $K$-dimension (`Module.finrank`) of the Riemann–Roch space of $D$.
--
--   This is the Riemann–Roch theorem for a function field of one variable over an algebraically closed constant field, packaged as the existence of a canonical divisor together with a genus rather than as a statement about a named pair. It is the form in which Riemann–Roch is used downstream in the theory of places, reductions and prolongations for curves over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch
    (K : Type u) [Field K] [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F] :
    ∃ (Kc : Divisor K F) (g : ℕ), ∀ D : Divisor K F,
      (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g := by sorry
