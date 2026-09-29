-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_invariantFieldOf_map_conj_eq_map_fracAct
-- name    : CerednikDrinfeld.Mumford.invariantFieldOf_map_conj_eq_map_fracAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/1028c538-72f0-5b9f-a0df-6dc196e93d00
-- title:
--   Invariant field of a conjugate subgroup is its translate
-- statement:
--   Let $K$ be a field, $G$ a group and $M$ a commutative ring that is a $K$-algebra and an integral domain, equipped with an action of $G$ by ring automorphisms which commute with the scalar action of $K$ (so $K \to M$ lands in the $G$-invariants). For $g \in G$, `fracAct G M g` denotes the automorphism of the fraction field $\operatorname{Frac} M$ obtained by extending the ring automorphism $m \mapsto g \cdot m$ of $M$ to fraction fields, and for a subgroup $\Gamma \le G$, `invariantFieldOf K G M Γ` denotes the subfield of $\operatorname{Frac} M$ consisting of those $x$ with $\gamma \cdot x = x$ for all $\gamma \in \Gamma$ (this is the underlying subfield of the intermediate field over $K$ cut out by the same condition). The assertion is that for every $g \in G$ and every subgroup $\Gamma \le G$, the invariant subfield attached to the image of $\Gamma$ under conjugation by $g$, i.e. to $g\Gamma g^{-1}$, coincides with the image of the invariant subfield attached to $\Gamma$ under the ring homomorphism underlying `fracAct G M g`, as subfields of $\operatorname{Frac} M$.
--
--   This is the elementary compatibility of invariant function fields with conjugation of the acting subgroup: the function field of the quotient by $g\Gamma g^{-1}$ is the $g$-translate of the function field of the quotient by $\Gamma$, the algebraic counterpart of the translation maps $\Gamma \backslash X \to g\Gamma g^{-1}\backslash X$ underlying Hecke correspondences. It is used in the construction of the intertwining maps for the Čerednik–Drinfeld descent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_invariantFieldOf_map_conj_eq_map_fracAct.lean

import Definitions.Def_CerednikDrinfeld_MumfordQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Mumford.invariantFieldOf_map_conj_eq_map_fracAct
    (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
    [MulSemiringAction G M] [SMulCommClass G K M] [IsDomain M] (g : G) (Γ : Subgroup G) :
    invariantFieldOf K G M (Γ.map (MulAut.conj g).toMonoidHom) =
      (invariantFieldOf K G M Γ).map (fracAct G M g).toRingHom := by sorry
