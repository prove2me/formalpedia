-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle
-- name    : CerednikDrinfeld.Mumford.apply_conj_eq_actZ_apply_of_apply_eq_pathCycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/8e5bcdd8-5b34-5f89-aafb-094bdbd9074a
-- title:
--   Equivariance of the cycle map under a normalising element
-- statement:
--   Let $K_0$ be a field and $R_0$ a discrete valuation domain with fraction field $K_0$, and let $\mathcal T =$ `BruhatTits.tree R₀ K₀` be the graph whose vertices are homothety classes of full $R_0$-lattices in $K_0^2$, two classes being adjacent when they have adjacent representatives. Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism, the action of $\mathrm{PGL}_2(K_0)$ on $\mathcal T$ being by graph automorphisms. Let $\Gamma \le G$ be a subgroup whose image $\rho(\Gamma)$ lies in `typePreserving`, i.e. every element of $\rho(\Gamma)$ fixes the parity $\operatorname{vertexType}(w) = d(w_0,w) \bmod 2$ of the distance to the standard vertex $w_0$, and let $\rho(\Gamma)$ likewise act on $\mathcal T$ by graph automorphisms. Let $E$, $V$ be finite types and $D$ a degeneracy datum on $(E,V)$, consisting of two maps $a,b : E \to V$ and weights $E \to \mathbb{Z}_{>0}$; `ribbonKernel D` is the submodule of $E \to \mathbb Z$ cut out by the two pushforward maps along $a$ and $b$. Let $eE$ identify $E$ with the set of $\rho(\Gamma)$-orbits of darts of $\mathcal T$ whose chosen representative has source of type $0$. Let $v_0$ be a vertex and $\Phi : \mathrm{Additive}(\rho(\Gamma)^{\mathrm{ab}}) \to \,$`ribbonKernel D` an additive map whose coefficient at $eE(e)$ on the class of $\gamma$ is, by hypothesis $h\Phi$, the value at $e$ of `pathCycle`, the signed count of darts in each orbit along a chosen path from $v_0$ to $\gamma \cdot v_0$ (zero if the two are not joined). Let $n \in G$ normalise the underlying set of $\Gamma$, let $\pi$ be a permutation of $E$ and $s \in \mathbb Z^{\times}$, subject to: if $\rho(n)$ preserves vertex types then $s = 1$ and the orbit indexed by $\pi(eE(e))$ is the orbit of $\rho(n)$ applied to the representative dart of $e$, while if $\rho(n)$ does not preserve vertex types then $s = -1$ and that orbit is the orbit of the reverse of that dart. Let $A$ be a $\mathbb Z$-linear automorphism of `ribbonKernel D` with $(Ax)(\pi e) = s\, x(e)$ for all $x$ and all $e \in E$. Then for all $\gamma, \gamma' \in \rho(\Gamma)$ with $\gamma' = \rho(n)\,\gamma\,\rho(n)^{-1}$ in $\mathrm{PGL}_2(K_0)$ one has $\Phi(\overline{\gamma'}) = A\,\Phi(\overline{\gamma})$.
--
--   This is the combinatorial naturality of the cycle map from the abelianisation of a type-preserving discrete subgroup to the cycle lattice of the quotient graph: conjugation by a normalising element acts on cycles through the signed permutation of edges it induces on the quotient. It is used in the construction of the theta/period datum attached to a Mumford quotient curve and in the statement that that period datum is equivariant for the normaliser.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_apply_conj_eq_actZ_apply_of_apply_eq_pathCycle.lean

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

theorem CerednikDrinfeld.Mumford.apply_conj_eq_actZ_apply_of_apply_eq_pathCycle

    (K₀ : Type) [Field K₀]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [Mumford.GraphAction PGL(2, K₀) (BruhatTits.tree R₀ K₀)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]

    (E V : Type) [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]
    (D : DegeneracyData E V)
    (eE : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} ≃ E)

    [DecidableEq (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (v₀ : LT.LatticeTree.Vertex R₀ K₀)
    (Φ : Additive (Abelianization ↥(Γ.map ρ)) →+ ↥(ribbonKernel D))
    (hΦ : ∀ γ : ↥(Γ.map ρ), ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
      ((Φ (Additive.ofMul (Abelianization.of γ)) : ↥(ribbonKernel D)) : E → ℤ) (eE e) =
        Mumford.pathCycle (BruhatTits.tree R₀ K₀) (fun e' : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0} => e'.1) v₀ γ e)

    (n : G) (hn : n ∈ Subgroup.normalizer ((Γ : Subgroup G) : Set G))
    (π : Equiv.Perm E) (s : ℤˣ)
    (hπ : ∀ e : {e : Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀) // Mumford.vertexType (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) e.out.fst = 0},
        (ρ n ∈ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → s = 1 ∧ (eE.symm (π (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out))) ∧
        (ρ n ∉ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀) → s = -1 ∧ (eE.symm (π (eE e))).1 = (Quotient.mk (MulAction.orbitRel ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀).Dart) (ρ n • e.1.out).symm)))
    (A : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))
    (hA : ∀ (x : ↥(ribbonKernel D)) (e : E), (A x : E → ℤ) (π e) = ((s : ℤˣ) : ℤ) * (x : E → ℤ) e) :
    ∀ γ γ' : ↥(Γ.map ρ), (γ' : PGL(2, K₀)) = ρ n * (γ : PGL(2, K₀)) * (ρ n)⁻¹ →
      Φ (Additive.ofMul (Abelianization.of γ')) = A (Φ (Additive.ofMul (Abelianization.of γ))) := by sorry
