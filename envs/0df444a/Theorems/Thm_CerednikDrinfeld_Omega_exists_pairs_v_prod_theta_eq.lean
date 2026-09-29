-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq
-- name    : CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/2eabdb8b-f7a3-5e8a-b381-9e76d60b4012
-- title:
--   Valuations of characters as valuations of theta products
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible with finite residue ring $R/(\varpi)$, and let $K$ be a complete algebraically closed field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to: $v(a) \le 1$ for every $a \in R$; every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$; the powers $v(\varpi)^N$ are eventually below any nonzero $\varepsilon \in \Gamma_0$; and for $v(x) < 1$ and $y \ne 0$ some power $v(x)^n$ is at most $v(y)$. Let $\varpi_1$ be a pseudo-uniformiser, i.e. an element of $K_0$ with $0 < v(\varpi_1) < 1$ whose powers bound every nonzero value from above and below, such that the affinoids $\mathrm{affinoid}\,\varpi_1\,n$ exhaust the Drinfel'd upper half plane $\Omega = K \setminus \mathrm{im}(K_0 \to K)$, and such that the ring of functions holomorphic on all these affinoids is a domain. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism from a group $G$ acting on the set of homothety classes of full $R$-lattices in $K_0^2$, preserving adjacency in the Bruhat–Tits tree, with the action given by $\rho$ ($g \cdot w = \rho(g)\cdot w$), all vertex stabilisers finite and of order of valuation $1$ in $K$, and finitely many vertex orbits; assume a $G$-invariant map $\tau$ from vertices to $\mathbb{Z}/2$ taking distinct values on adjacent vertices. Let $z_0 \in \Omega$ and let $\chi : G \to K^\times$ be any homomorphism. Then there exist $n \in \mathbb{N}$ and points $a_1,\dots,a_n, b_1,\dots,b_n \in \Omega$ with $\mathrm{pmoebius}(\rho(\gamma))(a_i) \ne z_0$ and $\mathrm{pmoebius}(\rho(\gamma))(b_i) \ne z_0$ for all $i$ and all $\gamma \in G$, such that for every $\beta \in G$
--   $$v\Bigl(\prod_{i=1}^n \mathrm{theta}\,\rho\,a_i\,b_i\,z_0\bigl(\mathrm{pmoebius}(\rho(\beta))(z_0)\bigr)\Bigr) = v(\chi(\beta)),$$
--   where $\mathrm{theta}\,\rho\,a\,b\,z_0$ is the product over $\gamma \in G$ of the factors $\mathrm{thetaFactor}\,\rho\,a\,b\,z_0\,z\,\gamma$ and $\mathrm{pmoebius}$ is the Möbius action of $\mathrm{PGL}_2(K_0)$ on $\mathbb{P}^1(K)$ read in the affine coordinate.
--
--   This is the value-group layer of Jacobi inversion for a cocompact tree lattice acting on the Drinfel'd upper half plane: an arbitrary character of $G$ is matched in absolute value by a finite product of Mumford theta multipliers based at $z_0$. It is used by [`CerednikDrinfeld.Omega.exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring`](thm.html#CerednikDrinfeld.Omega.exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring), where this layer is combined with the layers matching the residue and the principal-unit parts of a character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq.lean

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

theorem CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq
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

    (χ : G →* Kˣ) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      ∀ β : G, Valued.v (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) = Valued.v ((χ β : Kˣ) : K) := by sorry
