-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_points_prod_theta_eq_of_v_sub_one_lt
-- name    : CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/07843247-319c-53bb-b27b-de30541adc9e
-- title:
--   Principal-unit characters as finite products of theta multipliers
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible and assume $R/(\varpi)$ finite. Let $K$ be a complete, algebraically closed extension field of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero, such that: every element of $R$ has $v \le 1$ in $K$; every $a \in K_0$ with $v(a) \le 1$ is an integer of $R$; the powers $v(\varpi)^N$ are cofinal towards $0$; and for all $x$ with $v(x) < 1$ and all $y \ne 0$ some power $v(x)^n \le v(y)$. Let $\varpi_1$ be a pseudo-uniformiser, i.e. an element of $K_0$ with $0 < v(\varpi_1) < 1$ whose powers bound $v(a)$ above and below for every $a \neq 0$, assume its affinoids exhaust the Drinfeld upper half plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$, and assume the ring `holRing` of functions on $\Omega$ that on each affinoid are uniform limits of uniformly bounded pole-free rational functions is a domain. Let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ and an action on the homothety classes of full $R$-lattices in $K_0^2$ which preserves adjacency in the Bruhat–Tits tree and agrees with the action through $\rho$; assume all vertex stabilisers are finite, there are finitely many vertex orbits, there is a $G$-invariant map $\tau$ from vertices to $\mathbb{Z}/2$ taking distinct values on adjacent vertices, and $v$ of the cardinality of each stabiliser, viewed in $K$, equals $1$. Let $z_0 \in \Omega$, and let $\theta : G \to K^\times$ be a homomorphism with $v(\theta(\beta) - 1) < 1$ for all $\beta$ and $\theta(\gamma) = 1$ for every $\gamma$ of finite order. Then there are $n \in \mathbb{N}$ and points $a_1,\dots,a_n, b_1,\dots,b_n \in \Omega$ whose $\rho(G)$-orbits under `pmoebius` avoid $z_0$, such that for every $\beta \in G$ one has $\theta(\beta) = \prod_{i=1}^{n} \Theta(a_i, b_i; z_0; \rho(\beta) z_0)$, where $\Theta$ denotes `theta`, the product over $G$ of the factors `thetaFactor`.
--
--   This is Jacobi inversion for the analytic uniformisation of a Mumford quotient of Drinfeld's upper half plane, restricted to characters of $G$ with values in the principal units $\{v(x-1)<1\}$ and trivial on torsion: such a character is exactly a finite product of theta multipliers. It is the innermost of three successive layers used by [`CerednikDrinfeld.Omega.exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring`](thm.html#CerednikDrinfeld.Omega.exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring), which treats general characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_points_prod_theta_eq_of_v_sub_one_lt.lean

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
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt
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

    (z₀ : K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)

    (θ : G →* Kˣ) (hθ₁ : ∀ β : G, Valued.v (((θ β : Kˣ) : K) - 1) < 1) (hθ : ∀ γ : G, IsOfFinOrder γ → θ γ = 1) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      ∀ β : G, ((θ β : Kˣ) : K) = ∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀) := by sorry
