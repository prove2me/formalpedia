-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup
-- name    : CerednikDrinfeld.Mumford.exists_finiteHom_quotientDegeneracyData_of_subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/78030c08-62e7-596a-816d-21c09910542c
-- title:
--   Finite-index subgroups induce finite morphisms of quotient degeneracy data
-- statement:
--   Let $G$ be a group acting on a type $W$, let $\mathcal{T}$ be a simple graph on $W$ whose adjacency is preserved by $G$ (the `GraphAction` condition: $\mathcal{T}.\mathrm{Adj}\,v\,w$ implies $\mathcal{T}.\mathrm{Adj}\,(g\cdot v)\,(g\cdot w)$), and let $\Gamma'\le G$ be a subgroup of finite index which likewise acts on $\mathcal{T}$ by graph automorphisms. Assume every vertex stabiliser $\mathrm{Stab}_G(v)$ and every dart stabiliser $\mathrm{Stab}_G(d)$ is finite, that the $G$-orbits of darts and the $\Gamma'$-orbits of darts and of vertices each form a finite type, with the relevant decidable equalities. Attached to each of $G$ and $\Gamma'$ is the degeneracy datum whose edge set is the set of orbits of darts, whose vertex set is the set of orbits of vertices, whose two end-point maps are induced by $d\mapsto d.\mathrm{fst}$ and $d\mapsto d.\mathrm{snd}$, and whose width on a dart-orbit $e$ is $|\mathrm{Stab}(e.\mathrm{out})|$ for the chosen representative. The assertion is that there exists a `FiniteHom` $\mu$ from the $\Gamma'$-datum to the $G$-datum, i.e. maps $\mu_V,\mu_E$ compatible with both end-point maps, local degrees $\deg$ on dart-orbits and $\deg_V$ on vertex-orbits and a total degree $\deg_{\mathrm{tot}}$ in $\mathbb{N}^+$ satisfying the width law $w(\mu_E e)=\deg(e)\,w(e)$, the two harmonicity sums at $a$ and at $b$, and the vertex-fibre sum law, whose data are moreover pinned: $\mu_E(e')$ is the $G$-orbit of $e'.\mathrm{out}$, $\mu_V(v')$ is the $G$-orbit of $v'.\mathrm{out}$, $\deg(e')\cdot|\mathrm{Stab}_{\Gamma'}(e'.\mathrm{out})| = |\mathrm{Stab}_{G}(e'.\mathrm{out})|$, $\deg_V(v')\cdot|\mathrm{Stab}_{\Gamma'}(v'.\mathrm{out})| = |\mathrm{Stab}_{G}(v'.\mathrm{out})|$, and $\deg_{\mathrm{tot}} = [G:\Gamma']$.
--
--   This is the statement that the quotient graph of $\mathcal{T}$ by a finite-index subgroup covers the quotient by the whole group as a harmonic (finite) morphism of weighted graphs, with local degrees equal to the indices of the corresponding stabilisers and global degree the index of the subgroup. It feeds the comparison of quotient data for conjugate subgroups in [`CerednikDrinfeld.Mumford.exists_finiteHom_orientedQuotient_of_conj_le`](thm.html#CerednikDrinfeld.Mumford.exists_finiteHom_orientedQuotient_of_conj_le), within the graph-theoretic side of the Mumford-curve description used in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_finiteHom_quotientDegeneracyData_of_subgroup
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (Γ' : Subgroup G) [GraphAction (↥Γ') 𝒯] [Γ'.FiniteIndex]
    (hfinV : ∀ v : W, Finite (stabilizer G v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer G d))
    [Fintype (QuotEdge G 𝒯)] [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotVert G W)]
    [Fintype (QuotEdge (↥Γ') 𝒯)] [Fintype (QuotVert (↥Γ') W)] [DecidableEq (QuotVert (↥Γ') W)] :
    ∃ μ : (quotientDegeneracyData (↥Γ') 𝒯).FiniteHom (quotientDegeneracyData G 𝒯),
      (∀ e' : QuotEdge (↥Γ') 𝒯, μ.mapE e' = Quotient.mk (orbitRel G 𝒯.Dart) e'.out) ∧
      (∀ v' : QuotVert (↥Γ') W, μ.mapV v' = Quotient.mk (orbitRel G W) v'.out) ∧
      (∀ e' : QuotEdge (↥Γ') 𝒯,
        (μ.deg e' : ℕ) * Nat.card (stabilizer (↥Γ') e'.out) = Nat.card (stabilizer G e'.out)) ∧
      (∀ v' : QuotVert (↥Γ') W,
        (μ.degV v' : ℕ) * Nat.card (stabilizer (↥Γ') v'.out) = Nat.card (stabilizer G v'.out)) ∧
      (μ.degTotal : ℕ) = Γ'.index := by sorry
