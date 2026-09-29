-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq
-- name    : CerednikDrinfeld.Omega.exists_int_neighbours_sum_eq_zero_v_apply_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/b8d23a05-655b-5994-bb5d-95abd770e28a
-- title:
--   Integral jumps of v∘ F at neighbours of the standard vertex
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi\in R$ be irreducible, and assume the residue ring $R/(\varpi)$ is finite. Let $K$ be a complete algebraically closed extension field of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to: every element of $R$ has $v\le 1$ in $K$; every $a\in K_0$ with $v(a)\le 1$ lies in the image of $R$; the powers $v(\varpi)^N$ are cofinal towards $0$ in $\Gamma_0$; and for $x\in K$ with $v(x)<1$ and $y\neq 0$ some $v(x)^n\le v(y)$. Let $\varpi_1$ be a pseudo-uniformiser for $K_0\subset K$ (an element of $K_0$ with $0<v(\varpi_1)<1$ and the scaling property) whose underlying element is the image of $\varpi$, and let $F$ be a unit of the ring $\mathrm{holRing}\,\varpi_1$ of functions on $\Omega=K\setminus K_0$ that are, on each affinoid $\mathrm{affinoid}\,\varpi_1\,n$, uniform limits of uniformly bounded pole-free rational functions. Then there is $m:\mathrm{Vertex}\,R\,K_0\to\mathbb{Z}$ (vertices being homothety classes of full $R$-lattices in $K_0^2$) such that: for every finite set $S$ of vertices whose elements are exactly the neighbours of the standard vertex in the Bruhat–Tits tree, $\sum_{y\in S}m(y)=0$; and for every neighbour $y$ of the standard vertex, every $g\in \mathrm{GL}_2(K_0)$ with $g\cdot\mathrm{stdVertex}=y$, and all $w,w'$ in $\mathrm{affinoid}\,\varpi_1\,0=\{z: v(z)\le 1,\ v(z-a)\ge 1\ \text{for all } a\in K_0 \text{ with } v(a)\le 1\}$, one has $v\bigl(F(\bar g\cdot w)\bigr)=v\bigl(F(w')\bigr)\cdot v(\varpi)^{m(y)}$, where $\bar g$ is the image of $g$ in $\mathrm{PGL}_2(K_0)$ acting on $\Omega$ by Möbius transformations.
--
--   This is the argument principle, or harmonicity of $-\log|F|$ on the Bruhat–Tits tree, for an invertible rigid holomorphic function on Drinfeld's upper half plane, localised at the standard vertex: $v\circ F$ is constant on the standard fibre and on each of its translates by the neighbours of the standard vertex, consecutive values differ by an integral power of $v(\varpi)$, and the resulting integers sum to zero. It is used in the construction of theta functions for the Cerednik–Drinfeld uniformisation, being cited in the results on the ribbon kernel and on the behaviour of $v\circ\theta$ under Möbius translation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Omega.exists_int_neighbours_sum_eq_zero_v_apply_smul_eq
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ)
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) :
    ∃ m : LT.LatticeTree.Vertex R K₀ → ℤ,
      (∀ S : Finset (LT.LatticeTree.Vertex R K₀),
        (∀ y, y ∈ S ↔ (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y) → ∑ y ∈ S, m y = 0) ∧
      ∀ (y : LT.LatticeTree.Vertex R K₀), (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y →
        ∀ (g : GL (Fin 2) K₀), g • LT.LatticeTree.stdVertex R K₀ = y →
          ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
            Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
                ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
              Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
                Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (m y) := by sorry
