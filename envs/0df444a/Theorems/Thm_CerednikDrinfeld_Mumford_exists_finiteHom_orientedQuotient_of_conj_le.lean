-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_finiteHom_orientedQuotient_of_conj_le
-- name    : CerednikDrinfeld.Mumford.exists_finiteHom_orientedQuotient_of_conj_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/2b28bd53-6ad4-5a29-9d8d-923f3cdc1d1c
-- title:
--   Harmonic morphism of oriented quotient data from g⁻¹Xg≤ Y
-- statement:
--   Let a group $G$ act on a type $W$ carrying a simple graph $\mathcal T$ whose adjacency is preserved by the action, with $\mathcal T$ connected and $2$-colourable, and fix $w_0\in W$; for $w\in W$ put $\mathrm{vertexType}(w)=d_{\mathcal T}(w_0,w)\bmod 2$, and let $\mathrm{typePreserving}$ be the subgroup of elements fixing all vertex types. Let $X,Y\le G$ be type-preserving subgroups, $g$ a type-preserving element with $g^{-1}xg\in Y$ for all $x\in X$, and assume the relative index of $g^{-1}Xg$ in $Y$ is nonzero; assume all stabilisers in $Y$ of vertices and of darts are finite. Let $D$ on finite types $(E,V)$ and $D'$ on $(E',V')$ be degeneracy data (two end maps $a,b$ and a width $w$ valued in $\mathbb N_{>0}$) presented as oriented quotients: bijections $V\simeq W/X$, $E\simeq\{X\text{-orbits of darts whose chosen representative has source of type }0\}$ under which $a$, $b$ send an orbit to the $X$-orbit of the source, resp. target, of its representative and $w$ is the order of the $X$-stabiliser of that dart, and similarly for $D'$ with $Y$. Then there is a finite homomorphism $\mu:D\to D'$ (maps on vertices and edges commuting with $a$ and $b$, edge degrees with $D'.w(\mu e)=\deg(e)\,D.w(e)$, vertex degrees whose partial sums over each fibre of $a$ and of $b$ agree, and a total degree summing the vertex degrees over each fibre) such that $\mu$ sends the $X$-orbit of $v$ to the $Y$-orbit of $g^{-1}v$, sends an oriented $X$-orbit of darts to the $Y$-orbit of $g^{-1}$ applied to its representative, and has total degree equal to the relative index of $g^{-1}Xg$ in $Y$.
--
--   This is the graph-theoretic input for Hecke and degeneracy correspondences on Mumford-type quotients: conjugation by $g$ together with the inclusion $g^{-1}Xg\le Y$ induces a finite harmonic morphism of the oriented quotient graphs of $\mathcal T$ by $X$ and by $Y$, of degree the index. It is used in the construction of the quotient presentations and of the Hecke action attached to the descent data in the Čerednik–Drinfel'd part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_finiteHom_orientedQuotient_of_conj_le.lean

import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_finiteHom_orientedQuotient_of_conj_le
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W)
    (X Y : Subgroup G) (hX : X ≤ typePreserving G 𝒯 w₀) (hY : Y ≤ typePreserving G 𝒯 w₀)
    (g : G) (hg : g ∈ typePreserving G 𝒯 w₀)
    (hXY : ∀ x ∈ X, g⁻¹ * x * g ∈ Y)
    (hidx : (X.map (MulAut.conj g⁻¹).toMonoidHom).relIndex Y ≠ 0)
    (hfinV : ∀ v : W, Finite (stabilizer (↥Y) v)) (hfinD : ∀ d : 𝒯.Dart, Finite (stabilizer (↥Y) d))

    {E V E' V' : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
    [Fintype E'] [DecidableEq E'] [Fintype V'] [DecidableEq V']
    (D : DegeneracyData E V) (eV : QuotVert (↥X) W ≃ V) (eE : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} ≃ E)
    (hDa : ∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D.a (eE e) = eV (Quotient.mk (orbitRel (↥X) W) e.1.out.fst))
    (hDb : ∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D.b (eE e) = eV (Quotient.mk (orbitRel (↥X) W) e.1.out.snd))
    (hDw : ∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, (D.w (eE e) : ℕ) = Nat.card (stabilizer (↥X) e.1.out))
    (D' : DegeneracyData E' V') (eV' : QuotVert (↥Y) W ≃ V') (eE' : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0} ≃ E')
    (hDa' : ∀ e : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D'.a (eE' e) = eV' (Quotient.mk (orbitRel (↥Y) W) e.1.out.fst))
    (hDb' : ∀ e : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, D'.b (eE' e) = eV' (Quotient.mk (orbitRel (↥Y) W) e.1.out.snd))
    (hDw' : ∀ e : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}, (D'.w (eE' e) : ℕ) = Nat.card (stabilizer (↥Y) e.1.out)) :
    ∃ μ : D.FiniteHom D',
      (∀ v : W, μ.mapV (eV (Quotient.mk (orbitRel (↥X) W) v)) = eV' (Quotient.mk (orbitRel (↥Y) W) (g⁻¹ • v))) ∧
      (∀ e : {e : QuotEdge (↥X) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0},
        ((eE'.symm (μ.mapE (eE e))) : {e : QuotEdge (↥Y) 𝒯 // vertexType 𝒯 w₀ e.out.fst = 0}).1 = Quotient.mk (orbitRel (↥Y) 𝒯.Dart) (g⁻¹ • e.1.out)) ∧
      (μ.degTotal : ℕ) = (X.map (MulAut.conj g⁻¹).toMonoidHom).relIndex Y := by sorry
