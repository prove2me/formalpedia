-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
-- name    : CerednikDrinfeld.Omega.v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/a366852d-9b40-553b-b979-05fdd9bc74e9
-- title:
--   Period law for theta units at arbitrary affinoid points
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi \in R$ be irreducible with finite residue ring $R/(\varpi)$, and let $K$ be a field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero, complete and algebraically closed. The valuation is tied to $R$ by: $v$ is at most $1$ on the image of $R$; an element of $K_0$ with $v \le 1$ lies in $R$; the powers $v(\varpi)^N$ are cofinal downwards; and for $v(x) < 1$ and $y \ne 0$ some $v(x)^n \le v(y)$ (rank one). Let $\varpi_1$ be a pseudo-uniformiser such that every point of the Drinfeld upper half plane $\Omega = K \setminus K_0$ lies in some affinoid $\mathrm{affinoid}\ \varpi_1\ n$, with the ring $\mathrm{holRing}\ \varpi_1$ of functions $\Omega \to K$ whose restriction to each such affinoid is a bounded uniform limit of pole-free rational functions assumed to be a domain. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism, let $G$ act on the vertices of the Bruhat–Tits tree of $R$ (homothety classes of full lattices in $K_0^2$) preserving adjacency and through $\rho$, with all vertex stabilisers finite, finitely many vertex orbits, a $G$-invariant $\mathbb{Z}/2$-colouring $\tau$ of vertices taking distinct values on adjacent vertices, and $v$ of the order of every vertex stabiliser equal to $1$ (tameness). Let $E$ be a finite type equipped with an equivalence $eE$ onto the set of $G$-orbits of darts whose source has colour $0$. Let $a, z_1 \in \Omega$ with $z_1$ outside the $\rho(G)$-orbit of $a$ under the Möbius action, let $\beta \in G$, and let $U \in \mathrm{holRing}\ \varpi_1$ be a unit which at every $z \in \Omega$ outside the $\rho(G)$-orbit of $a$ agrees with $\mathrm{theta}\ \rho\ a\ (\rho(\beta)a)\ z_1$, the multipliable product over $\gamma \in G$ of the cross-ratios $(z, z_1; \rho(\gamma)a, \rho(\gamma)\beta a)$. Then for all $g, g' \in \mathrm{GL}_2(K_0)$, all $w, w'$ in the level-$0$ affinoid (those $z$ with $v(z) \le 1$ and $v(z-a) \ge 1$ for every $a \in K_0$ with $v(a) \le 1$) and every walk $p$ in the tree from $g \cdot v_0$ to $g' \cdot v_0$, where $v_0$ is the standard vertex,
--   $$v\bigl(U(\bar g' \cdot w')\bigr)\, v(\varpi)^{\sum_{e \in E} n_e\, c_\beta(e)\, [p](e)} = v\bigl(U(\bar g \cdot w)\bigr),$$
--   the points being moved by the images of $g, g'$ in $\mathrm{PGL}_2(K_0)$, where $n_e$ is $\mathrm{stabWidth}$ of the dart orbit $eE(e)$ (the order of the stabiliser of a chosen representative dart), $c_\beta = \mathrm{pathCycle}$ is the dart-orbit count of a chosen path from $v_0$ to $\beta \cdot v_0$, and $[p] = \mathrm{walkCycle}$ is the signed count of darts of $p$ in each orbit.
--
--   This is the multiplicative period relation for a theta unit on the Drinfeld upper half plane in the form used for Mumford curves: the valuation of the unit changes, between two vertices of the Bruhat–Tits tree, by the power of $v(\varpi)$ given by the stabiliser-weighted pairing of the cycle class of $\beta$ with the cycle class of any walk joining them. In contrast with the underlying single-dart statement for $\mathrm{theta}$ itself, no condition is imposed on the evaluation points $w, w'$ beyond lying in the level-$0$ affinoid, since a unit of the ring of holomorphic functions has constant valuation on each affinoid. It feeds the existence statements for valuations of theta products at a vertex and for the determinant of the matrix of cycle pairings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta.lean

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

theorem CerednikDrinfeld.Omega.v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
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

    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    [DecidableEq (LT.LatticeTree.Vertex R K₀)]

    {a z₁ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₁ : z₁ ∈ upperHalfPlane K₀ K)
    (hz₁a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₁) (β : G)
    (U : ↥(holRing ϖ₁)) (hU : IsUnit U)
    (hUθ : ∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) →
      (U : ↥(upperHalfPlane K₀ K) → K) z = theta ρ a (pmoebius K₀ (ρ β) a) z₁ (z : K))

    (g g' : GL (Fin 2) K₀) (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0)
    (p : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (g • LT.LatticeTree.stdVertex R K₀) (g' • LT.LatticeTree.stdVertex R K₀)) :
    Valued.v ((U : ↥(upperHalfPlane K₀ K) → K)
        ((Matrix.ProjGenLinGroup.mk g') • ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩)) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
          (∑ e : E, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
              (LT.LatticeTree.stdVertex R K₀) β e *
            CerednikDrinfeld.Mumford.walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1) p e) =
      Valued.v ((U : ↥(upperHalfPlane K₀ K) → K)
        ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) := by sorry
