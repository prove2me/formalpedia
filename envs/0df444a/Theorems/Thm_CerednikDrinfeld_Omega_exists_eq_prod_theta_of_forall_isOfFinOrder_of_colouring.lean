-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring
-- name    : CerednikDrinfeld.Omega.exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/3d7428c1-ae81-5701-bfb5-7a63bad8593e
-- title:
--   Characters as finite products of theta multipliers
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible and suppose $R/(\varpi)$ is finite; let $K$ be a field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed. It is assumed that $v \le 1$ on the image of $R$, that every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$, that the powers of $v(\varpi)$ are cofinal below every nonzero element of $\Gamma_0$, and that for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ one has $v(x)^n \le v(y)$ for some $n$ (rank one). Let $\varpi_1$ be a pseudo-uniformiser, i.e. an element of $K_0$ with $0 < v(\varpi_1) < 1$ whose powers bracket $v(a)$ for every $a \in K_0^\times$, assumed exhausting in the sense that every point of the Drinfeld upper half-plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$ lies in one of the affinoids of $\varpi_1$, and assume the ring of functions on $\Omega$ holomorphic on each of those affinoids is a domain. Let $G$ be a group, $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism, and let $G$ act on the set of homothety classes of full $R$-lattices in $K_0^2$ preserving adjacency in the Bruhat–Tits tree and through $\rho$, i.e. $g \cdot w = \rho(g) \cdot w$ for all $g$ and all vertices $w$. Assume all vertex stabilisers are finite, there are finitely many vertex orbits, there is a $G$-invariant colouring $\tau$ of the vertices by $\mathbb{Z}/2$ giving adjacent vertices different colours, and $v$ of the cardinality of each vertex stabiliser, viewed in $K$, equals $1$ (tameness). Let $\chi : G \to K^\times$ be a homomorphism with $\chi(\gamma) = 1$ for every $\gamma$ of finite order. Then there are $n \in \mathbb{N}$, points $a_1,\dots,a_n$, $b_1,\dots,b_n$ and $z_0$ in $\Omega$ such that no $\rho(\gamma) a_i$ and no $\rho(\gamma) b_i$ equals $z_0$, and for every $\beta \in G$, $\chi(\beta) = \prod_{i=1}^n \Theta(a_i, b_i; z_0)(\rho(\beta) z_0)$, where $\Theta$ denotes the theta function defined as the multipliable product over $G$ of the usual cross-ratio factors, and the action of $\mathrm{PGL}_2(K_0)$ on $K$ is the Möbius action on $\mathbb{P}^1(K)$ read in the affine coordinate.
--
--   This is the surjectivity half of the analytic (Jacobi inversion) description of the uniformisation of a Mumford curve attached to a cocompact tame tree lattice in $\mathrm{PGL}_2(K_0)$, phrased on characters of $G$ rather than on divisor classes: every character trivial on torsion is a finite product of theta multipliers. It is used in the construction of the torus uniformisation of the degree-zero Picard group of the Mumford quotient of Drinfeld's upper half-plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring.lean

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

theorem CerednikDrinfeld.Omega.exists_eq_prod_theta_of_forall_isOfFinOrder_of_colouring
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

    (χ : G →* Kˣ) (hχ : ∀ γ : G, IsOfFinOrder γ → χ γ = 1) :
    ∃ (n : ℕ) (a b : Fin n → K) (z₀ : K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧ z₀ ∈ upperHalfPlane K₀ K ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      ∀ β : G, ((χ β : Kˣ) : K) = ∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀) := by sorry
