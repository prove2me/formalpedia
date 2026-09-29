-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_existsUnique_ribbonKernel_hom_comp_eq_of_forall_mem_stabilizer
-- name    : CerednikDrinfeld.Mumford.existsUnique_ribbonKernel_hom_comp_eq_of_forall_mem_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/dbf70e11-490f-5fc9-ade0-398e51881e28
-- title:
--   Stabiliser-trivial characters factor uniquely through the cycle lattice
-- statement:
--   Let $K_0$ be a field which is the fraction field of a discrete valuation domain $R_0$, let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism, and let $\Gamma \le G$ be a subgroup whose image $\rho(\Gamma)$ lies in the type-preserving subgroup for the Bruhat–Tits tree on homothety classes of full $R_0$-lattices in $K_0^2$ (adjacency being the symmetrisation of `AdjacentLattice`), i.e. each element fixes the parity $\mathrm{dist}(v_{\mathrm{std}},\,\cdot\,) \bmod 2$ of the distance to the standard vertex, $\rho(\Gamma)$ acting on the tree by adjacency-preserving maps. Let $E, V$ be finite types, $D$ a degeneracy datum on $(E,V)$ (maps $a, b : E \to V$ and weights $E \to \mathbb{Z}_{>0}$), and fix bijections $eV$ from the set of $\rho(\Gamma)$-orbits of vertices to $V$ and $eE$ from the set of $\rho(\Gamma)$-orbits of darts whose chosen representative has type-$0$ origin to $E$, compatible with $D$ in the sense that $D.a(eE\,e)$ and $D.b(eE\,e)$ are the $eV$-labels of the orbits of the origin and the terminus of $e$. Fix a vertex $v_0$ and an additive map $\Phi$ from the abelianisation of $\rho(\Gamma)$, written additively, to the ribbon kernel of $D$ (the functions $E \to \mathbb{Z}$ killed by pushforward along both $a$ and $b$), such that for every $\gamma$ and every type-$0$ dart orbit $e$ the $eE\,e$-coordinate of $\Phi[\gamma]$ is the signed number of darts in the orbit $e$ occurring along a chosen path from $v_0$ to $\gamma v_0$. Then for every commutative ring $C$ and every homomorphism $c : \rho(\Gamma) \to C^\times$ which is trivial on the stabiliser of every vertex, there is exactly one $\mathbb{Z}$-linear map $u$ from the ribbon kernel of $D$ to $C^\times$ (written additively) with $u(\Phi[\gamma]) = c(\gamma)$ for all $\gamma \in \rho(\Gamma)$.
--
--   This is the abelianised form of the statement that a character of a tree lattice which is trivial on all vertex stabilisers factors uniquely through the first homology of the quotient graph, here presented as the ribbon kernel of the degeneracy datum describing that graph. With $C$ taken to be a complete algebraically closed field of the relevant residue characteristic, the unique factorisation produces a torus point, and the result is used in the construction of the uniformisation of the Jacobian of a Mumford quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_existsUnique_ribbonKernel_hom_comp_eq_of_forall_mem_stabilizer.lean

import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Mathlib.GroupTheory.Abelianization.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.existsUnique_ribbonKernel_hom_comp_eq_of_forall_mem_stabilizer

    (K₀ : Type) [Field K₀]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eV : Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀) ≃ V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.fst))
    (hDb : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) e.1.out.snd))

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (C : Type) [CommRing C]
    (c : ↥(Γ.map ρ) →* Cˣ)
    (hc : ∀ (w : LT.LatticeTree.Vertex R₀ K₀) (γ : ↥(Γ.map ρ)), γ ∈ MulAction.stabilizer ↥(Γ.map ρ) w → c γ = 1) :
    ∃! u : ↥(ribbonKernel D) →ₗ[ℤ] Additive Cˣ,
      ∀ γ : ↥(Γ.map ρ), u (Φ (Additive.ofMul (Abelianization.of γ))) = Additive.ofMul (c γ) := by sorry
