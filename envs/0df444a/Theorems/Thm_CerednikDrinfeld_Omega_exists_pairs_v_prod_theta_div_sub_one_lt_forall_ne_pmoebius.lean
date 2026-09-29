-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_div_sub_one_lt_forall_ne_pmoebius
-- name    : CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_div_sub_one_lt_forall_ne_pmoebius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/559f2ac7-5c7f-554e-abba-b3056ecc59d5
-- title:
--   Unit layer of Jacobi inversion for theta products, general position
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K_0$, let $\varpi \in R$ be irreducible with $R/(\varpi)$ finite, and let $K$ be a complete algebraically closed field, an algebra over $K_0$, valued in a linearly ordered commutative group with zero $\Gamma_0$, subject to: every element of $R$ has image of valuation $\le 1$ in $K$; every $a \in K_0$ whose image has valuation $\le 1$ is an integer of $R$; the powers of $v(\varpi)$ are cofinal below every nonzero $\varepsilon \in \Gamma_0$; and for $x$ with $v(x) < 1$ and $y \ne 0$ some power $v(x)^n$ is $\le v(y)$. Let $\varpi_1$ be a pseudo-uniformiser (an element of $K_0$ of valuation strictly between $0$ and $1$ whose powers bound the valuation of every nonzero element of $K_0$ from both sides) whose affinoids exhaust the Drinfeld upper half plane $\Omega = K \setminus \mathrm{image}(K_0)$, and assume the ring `holRing` of functions holomorphic on all these affinoids is a domain. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a group homomorphism, with $G$ acting on the set of homothety classes of full $R$-lattices in $K_0^2$ preserving adjacency in the Bruhat–Tits tree, the action being given by $\rho$ ($g \cdot w = \rho(g) \cdot w$), with all vertex stabilisers finite, finitely many vertex orbits, a $G$-invariant map $\tau$ from vertices to $\mathbb{Z}/2$ taking different values at adjacent vertices, and $v$ of the image in $K$ of the order of each vertex stabiliser equal to $1$. Let $z_0 \in \Omega$, let $\eta : G \to K^\times$ be a homomorphism with $v(\eta(\beta)) = 1$ for all $\beta$ and $\eta(\gamma) = 1$ for every $\gamma$ of finite order, and let $S$ be a finite set of points of $\Omega$. Then there exist $n$ and $a, b : \mathrm{Fin}\,n \to K$ with all $a_i, b_i \in \Omega$, such that $\rho(\gamma) a_i \ne z_0$ and $\rho(\gamma) b_i \ne z_0$ for all $i$ and all $\gamma \in G$ (the action being the fractional-linear action `pmoebius` on $K$, with $\infty$ sent to $0$), such that $a_i \ne \rho(\delta) s$ and $b_i \ne \rho(\delta) s$ for every $s \in S$, every $i$ and every $\delta \in G$, and such that for every $\beta \in G$ the product $\Theta_\beta = \prod_i \Theta(a_i, b_i; z_0)(\rho(\beta) z_0)$ of the theta functions `theta` (each an infinite product of theta factors over $G$) satisfies $v(\Theta_\beta) = 1$ and $v(\eta(\beta)/\Theta_\beta - 1) < 1$.
--
--   This is the middle of three layers in the Jacobi inversion argument for Mumford quotients of Drinfeld's upper half plane: a character of absolute value one on $G$ is realised by a finite product of theta multipliers up to principal units, with the extra general-position requirement that the chosen divisor points avoid the base point orbit and the orbits of a prescribed finite set. It is used in the assembly of the full Jacobi inversion statement [`CerednikDrinfeld.Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring`](thm.html#CerednikDrinfeld.Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring), and rests on the single-pair version together with finiteness of balls in the Bruhat–Tits tree and the path-cycle description of valuations of theta multipliers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_div_sub_one_lt_forall_ne_pmoebius.lean

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

theorem CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_div_sub_one_lt_forall_ne_pmoebius
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

    (η : G →* Kˣ) (hη₁ : ∀ β : G, Valued.v ((η β : Kˣ) : K) = 1) (hη : ∀ γ : G, IsOfFinOrder γ → η γ = 1)

    (S : Finset ↥(upperHalfPlane K₀ K)) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      (∀ s ∈ S, ∀ i (δ : G), a i ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b i ≠ pmoebius K₀ (ρ δ) (s : K)) ∧
      ∀ β : G, Valued.v (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) = 1 ∧
        Valued.v (((η β : Kˣ) : K) / (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) - 1) < 1 := by sorry
