-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_forall_ne_pmoebius
-- name    : CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq_forall_ne_pmoebius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/ceb198e2-34ed-58b3-b4e0-69d9bf0d6739
-- title:
--   Valuations of theta products realise any character, general position
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible with finite residue ring $R/(\varpi)$, and let $K$ be a complete, algebraically closed field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to: the images of elements of $R$ have $v \le 1$; conversely every $a \in K_0$ with $v(a) \le 1$ is an integer of $R$; the powers $v(\varpi)^N$ are cofinal towards $0$; and for $v(x) < 1$ and $y \ne 0$ some power $v(x)^n \le v(y)$. Let $\varpi_1$ be a pseudo-uniformiser (an element of $K_0$ with $0 < v(\varpi_1) < 1$ whose powers sandwich the valuation of every nonzero element of $K_0$) whose affinoids exhaust the Drinfeld upper half-plane $\Omega = K \setminus \mathrm{image}(K_0)$, and assume the ring `holRing` of functions on $\Omega$ that are, on each affinoid, uniform limits of uniformly bounded pole-free rational functions is a domain. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism from a group $G$ acting on the vertex set of the Bruhat–Tits tree of $R$, $K_0$ (homothety classes of full lattices) preserving adjacency and acting through $\rho$, with all vertex stabilisers finite, finitely many vertex orbits, and stabiliser orders of valuation $1$ in $K$; assume a $G$-invariant map $\tau$ from vertices to $\mathbb{Z}/2$ taking distinct values on adjacent vertices. Fix $z_0 \in \Omega$, a homomorphism $\chi : G \to K^\times$ and a finite set $S \subseteq \Omega$. Then there exist $n$ and points $a_1,\dots,a_n$, $b_1,\dots,b_n \in \Omega$ such that no $\rho(\gamma)$-Möbius image of any $a_i$ or $b_i$ equals $z_0$, no $a_i$ or $b_i$ equals a $\rho(\delta)$-Möbius image of a point of $S$, and for every $\beta \in G$, $v\bigl(\prod_{i} \Theta_\rho(a_i,b_i;z_0)(\rho(\beta) z_0)\bigr) = v(\chi(\beta))$, where $\Theta_\rho(a,b;z_0)$ is the theta function given by the product over $G$ of the associated theta factors.
--
--   This is the value-group layer of Jacobi inversion on a Mumford quotient of Drinfeld's upper half-plane: the absolute value of an arbitrary character of $G$ is matched exactly by the absolute value of a product of theta multipliers, with the additional general-position requirement that the chosen parameters avoid the $\rho(G)$-orbits of $z_0$ and of a prescribed finite set $S$. It feeds the construction of theta-function representations of characters used in the Cherednik–Drinfeld uniformisation, being cited by [`CerednikDrinfeld.Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring`](thm.html#CerednikDrinfeld.Omega.exists_eq_prod_theta_forall_ne_pmoebius_of_forall_isOfFinOrder_of_colouring) and [`CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq`](thm.html#CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_forall_ne_pmoebius.lean

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

theorem CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq_forall_ne_pmoebius
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

    (χ : G →* Kˣ)

    (S : Finset ↥(upperHalfPlane K₀ K)) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      (∀ s ∈ S, ∀ i (δ : G), a i ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b i ≠ pmoebius K₀ (ρ δ) (s : K)) ∧
      ∀ β : G, Valued.v (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) = Valued.v ((χ β : Kˣ) : K) := by sorry
