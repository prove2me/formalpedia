-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring
-- name    : CerednikDrinfeld.Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/939b6f72-ff93-55c1-b04d-c4dea4514ebf
-- title:
--   Jacobi inversion with multipliers, divisor avoiding prescribed orbits
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible with finite residue ring $R/(\varpi)$, and let $K$ be an algebraically closed field extension of $K_0$, complete for a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$. It is assumed that every element of $R$ has $v \le 1$ in $K$, that every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$, that the powers $v(\varpi)^N$ are cofinal below every nonzero element of $\Gamma_0$, and that for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ some power $v(x)^n$ is $\le v(y)$. Let $\varpi_1$ be a pseudo-uniformiser (an element of $K_0$ whose image has valuation strictly between $0$ and $1$, with every nonzero scalar sandwiched between powers of it) whose affinoids exhaust the Drinfeld upper half plane $\Omega = K \setminus \mathrm{im}(K_0 \to K)$, and assume the ring `holRing` $\varpi_1$ of functions holomorphic on all these affinoids is a domain. Let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}(2, K_0)$ and an action on the set of homothety classes of full $R$-lattices in $K_0^2$ which preserves adjacency in the Bruhat–Tits tree and is given by $g \cdot w = \rho(g) \cdot w$; assume all vertex stabilisers are finite, there are finitely many vertex orbits, there is a $G$-invariant colouring $\tau$ of the vertices by $\mathbb{Z}/2$ taking distinct values on adjacent vertices, and $v$ of the cardinality of each vertex stabiliser, viewed in $K$, equals $1$. Let $\chi : G \to K^\times$ be a homomorphism with $\chi(\gamma) = 1$ for every $\gamma$ of finite order, and let $S$ be a finite set of points of $\Omega$. Then there are $n \in \mathbb{N}$, points $a_1, \dots, a_n$, $b_1, \dots, b_n$ and $z_0$ in $\Omega$ such that $\rho(\gamma)$ applied to $a_i$, and likewise to $b_i$, never equals $z_0$ (for all $i$ and all $\gamma \in G$, the Möbius action `pmoebius` being used throughout), such that no $a_i$ and no $b_i$ lies in the orbit $\{\rho(\delta)s : \delta \in G\}$ of any $s \in S$, and such that for every $\beta \in G$ $$\chi(\beta) = \prod_{i=1}^{n} \Theta\bigl(a_i, b_i; z_0; \rho(\beta)z_0\bigr),$$ where $\Theta$ denotes `theta`, the product over $\gamma \in G$ of the corresponding theta factors.
--
--   This is Jacobi inversion in multiplier form for the Mumford quotient of Drinfeld's upper half plane: every character of $G$ trivial on torsion is realised as the multiplier system of a finite product of theta functions attached to pairs of points, here with the additional freedom that the representing divisor may be chosen with support off the $G$-orbits of any prescribed finite set. It is used in the construction of functions in the invariant field with prescribed vanishing behaviour, in particular for the statements controlling zeros, non-vanishing and orders at points with prescribed stabiliser cardinality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Mumford
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1)

    (χ : G →* Kˣ) (hχ : ∀ γ : G, IsOfFinOrder γ → χ γ = 1)

    (S : Finset ↥(upperHalfPlane K₀ K)) :
    ∃ (n : ℕ) (a b : Fin n → K) (z₀ : K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧ z₀ ∈ upperHalfPlane K₀ K ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      (∀ s ∈ S, ∀ i (δ : G), a i ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b i ≠ pmoebius K₀ (ρ δ) (s : K)) ∧
      ∀ β : G, ((χ β : Kˣ) : K) = ∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀) := by sorry
