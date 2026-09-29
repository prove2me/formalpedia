-- Prove2me | Theorems.Thm_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal
-- name    : AlgebraicCurve.RROpens.exists_effective_sub_add_smul_single_mem_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/0a80f96e-a6ab-534e-873c-8253512e811a
-- title:
--   Degree-zero classes as effective divisors minus g[P]
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra such that `HasPrincipalDivisors K F` holds, i.e. every nonzero $f \in F$ admits a finitely supported function $D_f$ on the places of $F/K$ with $D_f(v) = \operatorname{ord}_v f$ at every place and $\deg D_f = 0$. Here a place is a valuation subring of $F$ that contains the image of $K$, is not all of $F$ and is a principal ideal ring; its degree $\deg v$ is the $K$-dimension of its residue field, a divisor is a finitely supported $\mathbb{Z}$-valued function on places, and $\deg D = \sum_v D(v)\deg v$. Let $g$ be a natural number and $K_c$ a divisor such that the Riemann–Roch identity $\ell(D) - \ell(K_c - D) = \deg D + 1 - g$ holds for every divisor $D$, where $\ell(D)$ is the $K$-dimension of the Riemann–Roch space `riemannRochSpace D`. Let $P$ be a place with $\deg P = 1$ and let $A$ be a divisor with $\deg A = 0$. Then there is a divisor $E$ with $E(v) \ge 0$ for every place $v$ such that $E - (A + g\,[P])$ is principal, i.e. equals $v \mapsto \operatorname{ord}_v f$ for some nonzero $f \in F$.
--
--   This is the representability step underlying the construction of the Jacobian: modulo principal divisors, every degree-zero class is of the form $[E] - g[P]$ with $E$ effective, so that the degree-zero class group is covered by effective divisors of degree $g$ normalised at a rational base point. It is used in [`AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single`](thm.html#AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RROpens_exists_effective_sub_add_smul_single_mem_principal.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_effective_sub_add_smul_single_mem_principal
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (g : ℕ) (Kc : Divisor K F)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (hP : P.deg = 1) (A : Divisor K F) (hA : Divisor.degree A = 0) :
    ∃ E : Divisor K F, (∀ v, 0 ≤ E v) ∧
      E - (A + (g : ℤ) • Finsupp.single P 1) ∈ Divisor.principal (K := K) (F := F) := by sorry
