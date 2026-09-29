-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_monoidHom_eq_of_forall_isOfFinOrder_of_forall_apply_eq_of_span_pathCycle
-- name    : CerednikDrinfeld.Omega.monoidHom_eq_of_forall_isOfFinOrder_of_forall_apply_eq_of_span_pathCycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/32326c9b-9e28-5763-b403-0af573f8832b
-- title:
--   Torsion-killing characters determined by a spanning family of cycles
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$ and $\varpi \in R$ irreducible with finite residue ring $R/(\varpi)$, and let $K$ be a complete, algebraically closed field extension of $K_0$ carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, subject to the compatibility conditions that every element of $R$ has valuation at most $1$ in $K$, that every $a \in K_0$ of valuation at most $1$ is an integer of $R$ in the localisation sense, that powers of the valuation of $\varpi$ are cofinal below every nonzero $\varepsilon \in \Gamma_0$, and that for $v(x) < 1$ and $y \neq 0$ some power $v(x)^n$ is at most $v(y)$; let further $\varpi_1$ be a pseudo-uniformizer of $K_0$ in $K$ whose affinoids exhaust the Drinfeld upper half plane $K \setminus K_0$, with the ring of functions holomorphic on all those affinoids a domain. Let $G$ be a group with a homomorphism $\rho : G \to \mathrm{PGL}_2(K_0)$ and an action on the set of homothety classes of full $R$-lattices in $K_0^2$ which is by graph automorphisms of the Bruhat–Tits tree (adjacency induced by adjacency of lattice representatives) and which factors through $\rho$ in the sense $g \cdot w = \rho(g) \cdot w$. Assume all vertex stabilisers in $G$ are finite, the vertex orbit set is finite, and there is a $G$-invariant map $\tau$ from vertices to $\mathbb{Z}/2$ taking distinct values on adjacent vertices, with the cardinality of each vertex stabiliser of valuation $1$ in $K$. Let $E$ be a finite type in bijection (via `eE`) with the set of orbits of darts whose chosen representative has source of colour $0$. Finally let $\beta_1,\dots,\beta_r \in G$ be such that for every $\gamma \in G$ the integer vector on $E$ given by `pathCycle` at base point the standard vertex — the cycle vector read off a chosen path from the standard vertex to $\gamma \cdot$(standard vertex), or $0$ if none exists — is an integral linear combination of the corresponding vectors of the $\beta_j$. Then any two homomorphisms $\chi, \chi' : G \to K^\times$ that send every element of finite order to $1$ and satisfy $\chi(\beta_j) = \chi'(\beta_j)$ for all $j$ are equal.
--
--   This is the uniqueness half of the description of characters of a cocompact tame tree lattice in terms of Bass–Serre data: a character killing the torsion is determined by the induced homomorphism on the cycle lattice of the quotient graph, hence by its values on elements whose cycle vectors span. It is used in the construction of theta-like products on the Drinfeld upper half plane, in [`CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.exists_points_prod_theta_eq_of_v_sub_one_lt) and [`CerednikDrinfeld.Omega.exists_points_prod_theta_eq_forall_ne_pmoebius_of_v_sub_one_lt`](thm.html#CerednikDrinfeld.Omega.exists_points_prod_theta_eq_forall_ne_pmoebius_of_v_sub_one_lt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_monoidHom_eq_of_forall_isOfFinOrder_of_forall_apply_eq_of_span_pathCycle.lean

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

theorem CerednikDrinfeld.Omega.monoidHom_eq_of_forall_isOfFinOrder_of_forall_apply_eq_of_span_pathCycle
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

    {r : ℕ} (β : Fin r → G)
    (hspan : ∀ γ : G, ∃ n : Fin r → ℤ, ∀ e : E,
      CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
          (LT.LatticeTree.stdVertex R K₀) γ e
        = ∑ j, n j * CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
          (LT.LatticeTree.stdVertex R K₀) (β j) e)

    (χ χ' : G →* Kˣ) (hχ : ∀ γ : G, IsOfFinOrder γ → χ γ = 1) (hχ' : ∀ γ : G, IsOfFinOrder γ → χ' γ = 1)
    (heq : ∀ j : Fin r, χ (β j) = χ' (β j)) :
    χ = χ' := by sorry
