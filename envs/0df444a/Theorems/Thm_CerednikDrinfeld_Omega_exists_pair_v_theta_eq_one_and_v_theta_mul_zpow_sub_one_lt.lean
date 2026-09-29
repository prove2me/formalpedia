-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt
-- name    : CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/88531f59-ccc6-5be5-bf52-fc7ffb209b3f
-- title:
--   Theta multiplier with prescribed unit power along one edge orbit
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible with finite residue ring $R/(\varpi)$, and let $K$ be a field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed, with decidable equality. Assume: $v$ is $\le 1$ on the image of $R$; every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$ in $K_0$; the powers of $v(\varpi)$ are cofinal below every nonzero $\varepsilon \in \Gamma_0$; and for $x$ with $v(x) < 1$ and $y \ne 0$ some power $v(x)^n \le v(y)$. Let $\varpi_1$ be a pseudo-uniformizer (an element of $K_0$ whose valuation lies strictly between $0$ and $1$ and whose powers bracket the valuation of every nonzero element of $K_0$) whose associated affinoid exhaustion covers the Drinfeld upper half plane $\Omega = K \setminus \mathrm{image}(K_0)$, the ring of functions holomorphic on all these affinoids being a domain. Let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ and an action on the vertices (homothety classes of full $R$-lattices in $K_0^2$) of the Bruhat–Tits tree, preserving adjacency, and acting through $\rho$, i.e. $g \cdot w = \rho(g) \cdot w$ for all $g, w$; assume all vertex stabilisers are finite, there are finitely many vertex orbits, and there is a $G$-invariant $\mathbb{Z}/2$-colouring $\tau$ of vertices taking distinct values on adjacent vertices, with $v$ of the cardinality of each vertex stabiliser equal to $1$ (tameness). Fix $z_0 \in \Omega$, a finite type $E$ together with a bijection $eE$ onto the orbits of darts of the tree whose chosen representative has first vertex of colour $0$, an element $e_0 \in E$, and a unit $\zeta \in K^\times$ with $v(\zeta) = 1$. Then there exist $a, b \in \Omega$ with $\rho(\gamma) a \ne z_0$ and $\rho(\gamma) b \ne z_0$ for every $\gamma \in G$ (Möbius action on $K \cup \{\infty\}$, restricted to $K$), such that for every $\beta \in G$ the theta value $\Theta = \theta(\rho; a, b; z_0)(\rho(\beta) z_0)$, the convergent product over $G$ of the cross-ratio factors, satisfies $v(\Theta) = 1$ and $v\bigl(\Theta \cdot \zeta^{-w(e_0)\,\mathrm{pc}(\beta)_{e_0}} - 1\bigr) < 1$, where $w(e_0)$ is the order of the stabiliser of the chosen dart representing $eE(e_0)$ and $\mathrm{pc}(\beta)_{e_0}$ is the $e_0$-coefficient of the cycle of $\beta$, computed from a chosen path in the tree from the standard vertex to $\beta$ applied to it.
--
--   This is the analytic input to the period computation for Mumford curves: a prescribed valuation-one unit, raised to the power width times edge-cycle coefficient, is realised as a theta multiplier modulo principal units, for a single edge orbit and with no auxiliary character. It is used by [`CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_div_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_div_sub_one_lt), which combines such single-edge data over all edge orbits.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt.lean

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

theorem CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt
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
    (e₀ : E) (ζ : Kˣ) (hζ : Valued.v ((ζ : Kˣ) : K) = 1) :
    ∃ a b : K, a ∈ upperHalfPlane K₀ K ∧ b ∈ upperHalfPlane K₀ K ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) ∧ (∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) ∧
      ∀ β : G, Valued.v (theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) = 1 ∧
        Valued.v (theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) *
            (((ζ : Kˣ) : K) ^ (((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e₀).1 : ℕ) : ℤ) *
              CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
                (LT.LatticeTree.stdVertex R K₀) β e₀))⁻¹ - 1) < 1 := by sorry
