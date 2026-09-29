-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_isUnit_det_pathCycle_and_span_pathCycle
-- name    : CerednikDrinfeld.Omega.exists_isUnit_det_pathCycle_and_span_pathCycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/0fa1b4f6-c8b6-51d4-882c-572a65bc6a8c
-- title:
--   Unimodular cycle basis realised by group elements
-- statement:
--   Let $R$ be a discrete valuation domain with irreducible element $\varpi$ and finite residue ring $R/(\varpi)$, let $K_0$ be its fraction field, and let $K$ be an algebraically closed field extension of $K_0$, complete for a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to the compatibility hypotheses that $v\le 1$ on the image of $R$, that every $a\in K_0$ with $v(a)\le 1$ lies in the image of $R$, that the powers of $v(\varpi)$ are cofinal towards $0$ in $\Gamma_0$, and that for $v(x)<1$ and $y\ne0$ some power $v(x)^n$ is at most $v(y)$; let $\varpi_1$ be a pseudo-uniformiser (an element of $K_0$ of valuation strictly between $0$ and $1$ satisfying the stated two-sided scaling condition) whose affinoids exhaust the Drinfeld upper half-plane $K\setminus K_0$, with the associated ring of holomorphic functions a domain. Let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}(2,K_0)$ and an adjacency-preserving action on the vertices of the Bruhat–Tits tree of $R$ in $K_0$ (vertices being homothety classes of full lattices in $K_0^2$, adjacency as in [`CerednikDrinfeld.BruhatTits.tree`](def/CerednikDrinfeld_BruhatTitsTree.html#L83)) which agrees with the action through $\rho$; assume all vertex stabilisers are finite, the vertex orbit set is finite, and $v$ of the stabiliser orders, viewed in $K$, equals $1$. Let $\tau$ be a $G$-invariant $\mathbb{Z}/2$-colouring of vertices taking distinct values on adjacent vertices, and let $E$ be a finite type equipped with an equivalence $eE$ onto the set of $G$-orbits of darts whose source has colour $0$. Then there are $r\in\mathbb{N}$, elements $\beta_1,\dots,\beta_r$ of $G$ and an injection $\iota : \mathrm{Fin}\,r \to E$ such that the $r\times r$ integer matrix whose $(i,j)$ entry is the $\iota(i)$-component of $\mathrm{pathCycle}$ of $\beta_j$ — the signed count, along a path in the tree from the standard vertex to $\beta_j$ applied to it, of the dart orbits enumerated by $eE$ — has unit determinant, and such that for every $\gamma\in G$ there are integers $n_1,\dots,n_r$ with $\mathrm{pathCycle}(\gamma)(e) = \sum_j n_j\,\mathrm{pathCycle}(\beta_j)(e)$ for all $e\in E$.
--
--   This is the statement that, for a colour-preserving cocompact tame lattice $G$ acting on the Bruhat–Tits tree, the cycle vectors attached to group elements span a lattice of integer flows on the finite quotient graph admitting a basis realised by group elements $\beta_j$, unimodular on the edges off a spanning tree; it is the Bass–Serre fundamental-cycle input to the Mumford period computation. It is used in the construction of products of theta functions on the Drinfeld upper half-plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_isUnit_det_pathCycle_and_span_pathCycle.lean

import Mathlib
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
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_isUnit_det_pathCycle_and_span_pathCycle
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
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0}) :
    ∃ (r : ℕ) (β : Fin r → G) (ι : Fin r → E),
      Function.Injective ι ∧
      IsUnit (Matrix.of (fun i j : Fin r =>
        CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
          (LT.LatticeTree.stdVertex R K₀) (β j) (ι i))).det ∧
      ∀ γ : G, ∃ n : Fin r → ℤ, ∀ e : E,
        CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
            (LT.LatticeTree.stdVertex R K₀) γ e
          = ∑ j, n j * CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
            (LT.LatticeTree.stdVertex R K₀) (β j) e := by sorry
