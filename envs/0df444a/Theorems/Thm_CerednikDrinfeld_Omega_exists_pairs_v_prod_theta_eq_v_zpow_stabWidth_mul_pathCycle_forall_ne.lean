-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne
-- name    : CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/972dad3c-1907-54c3-a619-0cbad7622a33
-- title:
--   Theta multipliers realising a prescribed valuation on one dart orbit
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible with finite residue ring $R/(\varpi)$, and let $K$ be a complete, algebraically closed field extension of $K_0$ carrying a valuation $v$ with values in $\Gamma_0$. Assume: every element of $R$ has $v \le 1$ in $K$; every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$; the powers $v(\varpi)^N$ are cofinal below every nonzero $\varepsilon \in \Gamma_0$; and for $v(x) < 1$ and $y \neq 0$ some power $v(x)^n \le v(y)$ (rank one). Let $\varpi_1$ be a pseudo-uniformizer, i.e. an element of $K_0$ with $0 < v(\varpi_1) < 1$ whose powers bound the valuations of all nonzero elements of $K_0$ from both sides, assumed exhausted (every point of $\Omega = K \setminus K_0$ lies in some affinoid $\mathrm{affinoid}\,\varpi_1\,n$), with holomorphic ring a domain. Let $G$ be a group acting on the set of homothety classes of full $R$-lattices in $K_0^2$ preserving adjacency in the Bruhat–Tits tree, and let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism through which the action factors ($g \cdot w = \rho(g) \cdot w$). Assume all vertex stabilizers are finite, there are finitely many vertex orbits, there is a $G$-invariant map $\tau$ from vertices to $\mathbb{Z}/2$ taking distinct values on adjacent vertices, and each stabilizer order has valuation $1$ in $K$ (tameness). Fix $z_0 \in \Omega$, a finite type $E$ together with a bijection $eE$ onto the $G$-orbits of darts whose chosen representative has tail of colour $0$, an element $e \in E$, a nonzero $t \in K$, and a finite set $S$ of points of $\Omega$. Then there are $n \in \mathbb{N}$ and $a, b : \mathrm{Fin}\,n \to K$ with all $a_i, b_i \in \Omega$, such that no $G$-translate $\mathrm{pmoebius}(\rho\gamma)$ of any $a_i$ or $b_i$ equals $z_0$, no $a_i$ or $b_i$ equals a translate $\mathrm{pmoebius}(\rho\delta)(s)$ of a point $s \in S$, and for every $\beta \in G$ $$v\Bigl(\prod_i \Theta_\rho(a_i, b_i; z_0, \mathrm{pmoebius}(\rho\beta)(z_0))\Bigr) = v(t)^{\,w(eE(e))\cdot c_\beta(e)},$$ where $\Theta_\rho(a,b;z_0,z)$ is the infinite product over $\gamma \in G$ of the corresponding theta factors, $w(eE(e))$ is the cardinality of the stabilizer of the chosen dart representative of the orbit $eE(e)$ (as a positive natural number), and $c_\beta$ is the cycle $\mathrm{pathCycle}$ of $\beta$ computed from a walk in the tree from the standard vertex to $\beta \cdot (\text{standard vertex})$, with the darts indexed through $eE$, evaluated at $e$.
--
--   This is the single-orbit building block of the valuation step in the theta-period (Jacobi inversion) analysis for Mumford uniformisation: it realises the prescribed value $v(t)$ raised to the flow of $\beta$ through one dart orbit, weighted by the dart stabilizer, as the absolute value of a product of theta multipliers, while keeping the chosen pairs off finitely many prescribed orbits. It is used by [`CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq_forall_ne_pmoebius`](thm.html#CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq_forall_ne_pmoebius), which combines the orbits of darts to match an arbitrary prescribed character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Mumford
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne
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

    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (e : E) (t : K) (ht : t ≠ 0)

    (S : Finset ↥(upperHalfPlane K₀ K)) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      (∀ s ∈ S, ∀ i (δ : G), a i ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b i ≠ pmoebius K₀ (ρ δ) (s : K)) ∧
      ∀ β : G, Valued.v (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) =
        Valued.v t ^ (((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
          CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
            (LT.LatticeTree.stdVertex R K₀) β e) := by sorry
