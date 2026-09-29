-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_isSchottky_le_map_normal_relIndex_ne_zero_of_even
-- name    : CerednikDrinfeld.exists_isSchottky_le_map_normal_relIndex_ne_zero_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/76eea376-3fb1-5eb7-81d6-e6b15b8dfc5b
-- title:
--   Finite-index Schottky subgroup inside the image of the even part
-- statement:
--   Let $r$ be a prime, let $\mathcal O$ be a characteristic-zero integral domain which is a discrete valuation ring, let $\pi \in \mathcal O$ be irreducible with $\mathcal O/(\pi)$ of cardinality $r$, and let $K_0$ be a characteristic-zero field that is a fraction field of $\mathcal O$. Let $v\det : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively) be a group homomorphism satisfying $v\det(g) = n$ if and only if $\det g = u\,\pi^{n}$ in $K_0$ for some unit $u$ of $\mathcal O$. Let $G$ be a group with homomorphisms $\sigma : G \to \mathrm{GL}_2(K_0)$ and $\rho : G \to \mathrm{PGL}_2(K_0)$ such that $\rho(g)$ is the class of $\sigma(g)$, let $\Gamma \le G$, and let $\Gamma' \le G$ consist exactly of those $x \in \Gamma$ with $v\det(\sigma x)$ even. Assume that for every vertex $v$ of the lattice tree (a homothety class of full $\mathcal O$-lattices in $K_0^2$) the set of elements of $\rho(\Gamma')$ fixing $v$ is finite, and that some finite set $S$ of vertices meets every $\rho(\Gamma')$-orbit. Then there is a subgroup $N \le \rho(\Gamma')$ of $\mathrm{PGL}_2(K_0)$ such that $N$, viewed inside $\rho(\Gamma)$, is normal there, the relative index of $N$ in $\rho(\Gamma')$ is non-zero, and $N$ is Schottky for the Bruhat–Tits tree on vertices, i.e. every vertex stabiliser in $N$ is trivial, no element of $N$ carries a dart to its reverse, and the sets of $N$-orbits of vertices and of darts are finite.
--
--   This is the group-theoretic input to Mumford's uniformisation for the Čerednik–Drinfeld description: from a discrete, cocompact action of the image of the even part of $\Gamma$ on the Bruhat–Tits tree of $\mathrm{PGL}_2(K_0)$ one extracts a finite-index Schottky subgroup, normal in the image of all of $\Gamma$ so that the quotient curve carries the residual action. It is used in the construction of the formal quotient datum whose coefficients give the $p$-adic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_isSchottky_le_map_normal_relIndex_ne_zero_of_even.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford CerednikDrinfeld.BruhatTits

theorem CerednikDrinfeld.exists_isSchottky_le_map_normal_relIndex_ne_zero_of_even
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))
    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S) :
    ∃ N : Subgroup (PGL(2, K₀)), N ≤ Γ'.map ρ ∧ (N.subgroupOf (Γ.map ρ)).Normal ∧ N.relIndex (Γ'.map ρ) ≠ 0 ∧
      IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀) := by sorry
