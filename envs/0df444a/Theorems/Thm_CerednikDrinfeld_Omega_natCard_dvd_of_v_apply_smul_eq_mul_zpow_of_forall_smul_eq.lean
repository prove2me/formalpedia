-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq
-- name    : CerednikDrinfeld.Omega.natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/2a85b4d5-e4e4-508a-bfff-709d71c5a15f
-- title:
--   Tame fixed edge stabiliser order divides the fibre jump
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible with $R/(\varpi)$ finite, and let $K$ be a complete, algebraically closed valued extension field of $K_0$ with value group $\Gamma_0$, subject to: the image of every element of $R$ has valuation $\le 1$; every $a \in K_0$ whose image has valuation $\le 1$ lies in the image of $R$; the powers of $v(\varpi)$ are cofinal towards $0$ in $\Gamma_0$; and for $v(x) < 1$ and $y \neq 0$ some power $v(x)^n$ is $\le v(y)$. Let $\varpi_1$ be a pseudo-uniformiser of $K_0$ in $K$ (an element of valuation strictly between $0$ and $1$ whose powers bound every valuation from both sides) whose underlying element is the image of $\varpi$. Let $F$ be a unit of the ring `holRing` of functions on $\Omega = K \setminus K_0$ that are uniform limits of uniformly bounded pole-free rational functions on each affinoid $\mathrm{affinoid}\,\varpi_1\,n$. Let $y$ be a vertex of the Bruhat–Tits tree of homothety classes of full $R$-lattices in $K_0^2$ adjacent to the class of the standard lattice, and let $H \le \mathrm{PGL}_2(K_0)$ be a finite subgroup fixing both vertices, with $v(\#H \cdot 1_K) = 1$ and $F(h \cdot z) = F(z)$ for all $h \in H$, $z \in \Omega$. Suppose $m \in \mathbb{Z}$ satisfies: for every $g \in \mathrm{GL}_2(K_0)$ with $g \cdot [R^2] = y$ and all $w, w'$ in $\mathrm{affinoid}\,\varpi_1\,0$ (the set of $z$ with $v(z) \le 1$ and $v(z - a) \ge 1$ for every $a \in K_0$ with $v(a) \le 1$), one has $v(F(g \cdot w)) = v(F(w')) \cdot v(\varpi)^m$. Then $\#H$ divides $m$ in $\mathbb{Z}$.
--
--   This is the divisibility of the jump of $v \circ F$ across an edge of the Bruhat–Tits tree by the order of a tame finite subgroup fixing that edge, stated in terms of fibres over the two endpoints rather than over the open edge tube. It feeds the construction of units on the Drinfel'd upper half-plane with prescribed behaviour along the tree, being cited by [`CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder`](thm.html#CerednikDrinfeld.Omega.exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Omega.natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ)
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F)
    (y : LT.LatticeTree.Vertex R K₀) (hy : (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y)
    (H : Subgroup PGL(2, K₀)) [Finite ↥H]
    (hH0 : ∀ h ∈ H, h • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀)
    (hHy : ∀ h ∈ H, h • y = y)
    (htame : Valued.v ((Nat.card ↥H : ℕ) : K) = 1)
    (hinv : ∀ h ∈ H, ∀ z : ↥(upperHalfPlane K₀ K),
      (F : ↥(upperHalfPlane K₀ K) → K) (h • z) = (F : ↥(upperHalfPlane K₀ K) → K) z)
    (m : ℤ)
    (hm : ∀ (g : GL (Fin 2) K₀), g • LT.LatticeTree.stdVertex R K₀ = y →
      ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
            ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
            Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ m) :
    ((Nat.card ↥H : ℕ) : ℤ) ∣ m := by sorry
