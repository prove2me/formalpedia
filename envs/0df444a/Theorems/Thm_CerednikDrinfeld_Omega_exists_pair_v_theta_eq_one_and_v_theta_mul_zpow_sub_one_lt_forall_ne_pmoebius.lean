-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius
-- name    : CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/33f3bb6f-b5d3-5eeb-9bde-782f2fcd2448
-- title:
--   Theta multipliers realising a prescribed unit, avoiding given orbits
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible with finite residue ring $R/(\varpi)$, and let $K$ be a field extension of $K_0$ with decidable equality, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed. Assume: every element of $R$ has $v \le 1$ in $K$; every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$; the powers $v(\varpi)^N$ are cofinal towards $0$ in $\Gamma_0$; and for $v(x) < 1$ and $y \ne 0$ some power $v(x)^n \le v(y)$ (a rank-one condition). Let $\varpi_1$ be a pseudo-uniformizer, i.e. an element of $K_0$ whose image has $0 < v < 1$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi_1)^N \le v(a) \le v(\varpi_1)^{-N}$ for some $N$, assume its affinoids exhaust the Drinfeld upper half plane $\Omega = K \setminus \mathrm{im}(K_0 \to K)$, and assume the ring `holRing` of functions holomorphic on all these affinoids is a domain. Let $G$ be a group with $\rho : G \to \mathrm{PGL}(2,K_0)$, acting on the vertices of the Bruhat–Tits tree of $R$, $K_0$ preserving adjacency and acting through $\rho$ (i.e. $g \cdot w = \rho(g) \cdot w$); assume all vertex stabilisers are finite, the orbit set of vertices is finite, and there is a $G$-invariant map $\tau$ from vertices to $\mathbb{Z}/2$ separating adjacent vertices, with $v(\#\mathrm{Stab}_G(w)) = 1$ for every vertex $w$ (tameness). Fix $z_0 \in \Omega$, a finite type $E$ with an equivalence $eE$ onto the set of dart orbits $e$ with $\tau(e.\mathrm{out}.\mathrm{fst}) = 0$, an element $e_0 \in E$, a unit $\zeta \in K^\times$ with $v(\zeta) = 1$, and a finite set $S$ of points of $\Omega$. Then there exist $a, b \in \Omega$ such that $\mathrm{pmoebius}(\rho\gamma)(a) \ne z_0$ and $\mathrm{pmoebius}(\rho\gamma)(b) \ne z_0$ for all $\gamma \in G$, such that $a$ and $b$ differ from $\mathrm{pmoebius}(\rho\delta)(s)$ for every $s \in S$ and $\delta \in G$, and such that for every $\beta \in G$ the theta value $\Theta = \mathrm{theta}\,\rho\,a\,b\,z_0\,(\mathrm{pmoebius}(\rho\beta)(z_0))$, the convergent product of the theta factors over $G$, satisfies $v(\Theta) = 1$ and $v\bigl(\Theta \cdot (\zeta^{\,w(e_0)\cdot \mathrm{pc}(\beta)_{e_0}})^{-1} - 1\bigr) < 1$, where $w(e_0)$ is the cardinality of the stabiliser of a representative dart of the orbit $(eE\,e_0)$ and $\mathrm{pc}(\beta)_{e_0}$ is the $e_0$-coefficient of the cycle `pathCycle` of $\beta$, computed along a path from the standard vertex to its $\beta$-translate (zero if the two are not joined).
--
--   This is the period-type computation of Manin–Drinfeld for a tame cocompact tree lattice: a pair of base points in $\Omega$, generic enough to avoid the orbits of $z_0$ and of a prescribed finite set $S$, whose theta function has unit values whose residues realise a prescribed power of $\zeta$, the exponent being the width of a chosen oriented quotient edge times the homology coefficient of $\beta$ at that edge. It is used, at $S = \varnothing$, by [`CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt), and with $S$ nonempty in the multi-edge statement [`CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_div_sub_one_lt_forall_ne_pmoebius`](thm.html#CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_div_sub_one_lt_forall_ne_pmoebius) forming the residue layer of the Jacobi inversion step for Mumford curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius.lean

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

theorem CerednikDrinfeld.Omega.exists_pair_v_theta_eq_one_and_v_theta_mul_zpow_sub_one_lt_forall_ne_pmoebius
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
    (e₀ : E) (ζ : Kˣ) (hζ : Valued.v ((ζ : Kˣ) : K) = 1)

    (S : Finset ↥(upperHalfPlane K₀ K)) :
    ∃ a b : K, a ∈ upperHalfPlane K₀ K ∧ b ∈ upperHalfPlane K₀ K ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) ∧ (∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) ∧
      (∀ s ∈ S, ∀ (δ : G), a ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b ≠ pmoebius K₀ (ρ δ) (s : K)) ∧
      ∀ β : G, Valued.v (theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) = 1 ∧
        Valued.v (theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) *
            (((ζ : Kˣ) : K) ^ (((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e₀).1 : ℕ) : ℤ) *
              CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
                (LT.LatticeTree.stdVertex R K₀) β e₀))⁻¹ - 1) < 1 := by sorry
