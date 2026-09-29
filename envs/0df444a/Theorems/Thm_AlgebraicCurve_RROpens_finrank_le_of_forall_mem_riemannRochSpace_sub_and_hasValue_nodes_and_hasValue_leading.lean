-- Prove2me | Theorems.Thm_AlgebraicCurve_RROpens_finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading
-- name    : AlgebraicCurve.RROpens.finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/862c185d-8b0e-510a-aa8e-589aa1ffb272
-- title:
--   Dimension bound for two Riemann–Roch spaces glued with a twist
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$ which is a curve over $K$ in the project's sense: every nonzero $f \in F$ has a degree-zero divisor recording its orders at all places, each residue field $\kappa(v)$ is finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Here a divisor is a finitely supported function on places, $\deg D = \sum_v D(v)\,[\kappa(v):K]$, the Riemann–Roch space of $D$ consists of the $f$ with $\operatorname{ord}_v f \ge -D(v)$ at every place, $\ell(D)$ is its $K$-dimension, and $v$ takes the value $c \in K$ at $g$ when $g$ lies in the valuation ring of $v$ and reduces to the image of $c$ in $\kappa(v)$. Fix a divisor $K_c$ and $g \in \mathbb{N}$ such that $\ell(D) - \ell(K_c - D) = \deg D + 1 - g$ for all $D$. Let $SS$ be a finite set of pairs of places whose first coordinates are pairwise distinct, let $s \in SS$, let $D_1, D_2$ be divisors vanishing at the first, respectively second, coordinates of all pairs in $SS$, let $x, y \in F$ satisfy $\operatorname{ord}_{s_1} x = 1$, $\operatorname{ord}_{s_2} y = 1$, let $u \in K$ and let $m, k \ge 0$ be integers with $2g + m + \#SS \le \deg D_1$ and $2g + k + \#SS \le \deg D_2$. Let $P$ be any $K$-submodule of $F^2$ all of whose elements $h$ satisfy: $h_0$ lies in the Riemann–Roch space of $D_1 - m\,s_1$, $h_1$ in that of $D_2 - k\,s_2$; for every $t \in SS$ with $t \ne s$ there is $c \in K$ with $h_0$ taking the value $c$ at $t_1$ and $h_1$ the value $c$ at $t_2$; and there is $\lambda \in K$ with $h_1 y^{-k}$ taking the value $\lambda$ at $s_2$ and $h_0 x^{-m}$ the value $u\lambda$ at $s_1$. Then $P$ is finite dimensional over $K$ and $\dim_K P \le (\deg D_1 - m) + (\deg D_2 - k) + 2 - 2g - \#SS$.
--
--   This is the elementary count $h^0 = h^0(C_1) + h^0(C_2) - \#\{\text{nodes}\}$ for a sheaf of large bidegree on two curves glued transversally at finitely many points, with the identification at one node twisted by a unit $u$, stated as an upper bound for an arbitrary space of pairs of sections satisfying the gluing conditions. It is used in the analysis of the special fibre of a twisted sheaf on the Deligne–Rapoport model of $X_H(M)$ at a prime exactly dividing the level, where that fibre appears as two copies of a curve of lower level crossing at the supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RROpens_finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.finrank_le_of_forall_mem_riemannRochSpace_sub_and_hasValue_nodes_and_hasValue_leading
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (SS : Finset (Place K F × Place K F))
    (hinj : Set.InjOn Prod.fst (SS : Set (Place K F × Place K F)))
    (s : Place K F × Place K F) (hs : s ∈ SS)
    (D₁ D₂ : Divisor K F) (hD₁ : ∀ t ∈ SS, D₁ t.1 = 0) (hD₂ : ∀ t ∈ SS, D₂ t.2 = 0)
    (x y : F) (hx : s.1.ord x = 1) (hy : s.2.ord y = 1)
    (u : K) (m k : ℤ) (hm : 0 ≤ m) (hk : 0 ≤ k)
    (hdeg₁ : 2 * (g : ℤ) + m + SS.card ≤ Divisor.degree D₁)
    (hdeg₂ : 2 * (g : ℤ) + k + SS.card ≤ Divisor.degree D₂)
    (P : Submodule K (Fin 2 → F))
    (hP : ∀ h ∈ P,
      h 0 ∈ riemannRochSpace (D₁ - Finsupp.single s.1 m) ∧
      h 1 ∈ riemannRochSpace (D₂ - Finsupp.single s.2 k) ∧
      (∀ t ∈ SS, t ≠ s → ∃ c : K, t.1.HasValue (h 0) c ∧ t.2.HasValue (h 1) c) ∧
      (∃ lam : K, s.2.HasValue (h 1 * y ^ (-k)) lam ∧ s.1.HasValue (h 0 * x ^ (-m)) (u * lam))) :
    FiniteDimensional K ↥P ∧
      (Module.finrank K ↥P : ℤ) ≤
        (Divisor.degree D₁ - m) + (Divisor.degree D₂ - k) + 2 - 2 * (g : ℤ) - SS.card := by sorry
