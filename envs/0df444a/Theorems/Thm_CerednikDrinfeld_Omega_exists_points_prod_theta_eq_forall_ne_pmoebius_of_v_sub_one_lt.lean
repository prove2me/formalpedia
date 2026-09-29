-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_points_prod_theta_eq_forall_ne_pmoebius_of_v_sub_one_lt
-- name    : CerednikDrinfeld.Omega.exists_points_prod_theta_eq_forall_ne_pmoebius_of_v_sub_one_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/e95ff5c1-d1f2-55f0-adaa-e191af3feff5
-- title:
--   Principal-unit characters as theta products avoiding prescribed orbits
-- statement:
--   Let $R$ be a discrete valuation domain with an irreducible element $\varpi$ and finite residue ring $R/(\varpi)$, let $K_0$ be its fraction field, and let $K$ be a $K_0$-algebra field carrying a valuation $v$ with values in a linearly ordered commutative group with zero, $K$ being complete and algebraically closed. Assume: $v$ is at most $1$ on the image of $R$; an element of $K_0$ with $v \le 1$ in $K$ is an $R$-integer; the powers of $v(\varpi)$ are cofinal below every nonzero value; and for $v(x) < 1$ and $y \neq 0$ some power $v(x)^n \le v(y)$. Let $\varpi_1$ be a pseudo-uniformiser (an element of $K_0$ with $0 < v < 1$ satisfying the scaling condition) whose affinoids exhaust the Drinfeld upper half plane $\Omega = K \setminus \mathrm{image}(K_0)$, with `holRing` $\varpi_1$ a domain. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism, with $G$ acting on the set of homothety classes of full lattices (the vertices of the Bruhat–Tits tree of $R$, $K_0$) preserving adjacency and through $\rho$, i.e. $g \cdot w = \rho(g) \cdot w$; assume all vertex stabilisers are finite, there are finitely many vertex orbits, and $v$ of the cardinality of each stabiliser equals $1$. Assume a $G$-invariant map $\tau$ from vertices to $\mathbb{Z}/2$ takes different values at adjacent vertices. Let $z_0 \in \Omega$, let $\theta : G \to K^\times$ be a homomorphism with $v(\theta(\beta) - 1) < 1$ for all $\beta$ and $\theta(\gamma) = 1$ for every $\gamma$ of finite order, and let $S$ be a finite set of points of $\Omega$. Then there are $n \in \mathbb{N}$ and points $a_1, \dots, a_n, b_1, \dots, b_n \in \Omega$ such that $\rho(\gamma) a_i \neq z_0$ and $\rho(\gamma) b_i \neq z_0$ for all $\gamma \in G$ (Möbius action via `pmoebius`), such that $a_i \neq \rho(\delta) s$ and $b_i \neq \rho(\delta) s$ for every $s \in S$ and $\delta \in G$, and such that $\theta(\beta) = \prod_{i} \Theta(a_i, b_i; z_0; \rho(\beta) z_0)$ for all $\beta \in G$, where $\Theta$ is the infinite product `theta` over $G$ of the theta factors.
--
--   This is the principal-unit layer of Jacobi inversion for a Mumford quotient of Drinfeld's upper half plane: characters of $G$ taking values in the principal units $\{v(x-1)<1\}$ are realised exactly as finite products of theta multipliers, with the divisor points chosen in general position so as to avoid the $\rho(G)$-orbit of $z_0$ and the orbits of a prescribed finite set. It is the step used by [`CerednikDrinfeld.Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring`](thm.html#CerednikDrinfeld.Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring) in the construction of the period lattice of the Mumford curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_points_prod_theta_eq_forall_ne_pmoebius_of_v_sub_one_lt.lean

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

theorem CerednikDrinfeld.Omega.exists_points_prod_theta_eq_forall_ne_pmoebius_of_v_sub_one_lt
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

    (θ : G →* Kˣ) (hθ₁ : ∀ β : G, Valued.v (((θ β : Kˣ) : K) - 1) < 1) (hθ : ∀ γ : G, IsOfFinOrder γ → θ γ = 1)

    (S : Finset ↥(upperHalfPlane K₀ K)) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      (∀ s ∈ S, ∀ i (δ : G), a i ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b i ≠ pmoebius K₀ (ρ δ) (s : K)) ∧
      ∀ β : G, ((θ β : Kˣ) : K) = ∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀) := by sorry
