-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsIsomorphic_map_ringHom
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsIsomorphic.map_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/c23f9326-78f2-50dd-91a1-08d47bbce979
-- title:
--   Isomorphism of rigidified formal mathcal O_D-modules is stable under base change
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring and $\Phi$ a formal $\mathcal O_D$-module over $O/pO$ (in the sense of the structure `FormalODModule`: a two-dimensional commutative formal group law $F$ together with an action of $\mathbb Z_{p^2}$ and an element $\varpi$, all given by pairs of power series that are law homomorphisms of $F$, with the usual multiplicativity, additivity, $\varpi\circ\varpi=[p]$ and $\varpi\circ a=\sigma(a)\circ\varpi$ relations), and let $g : B \to B'$ be a homomorphism of commutative rings. Let $t=(X,n,\rho)$ and $t'=(X',n',\rho')$ be rigidified objects over $B$, i.e. each consists of a formal $\mathcal O_D$-module over $B$, a natural number, and a pair $\rho$ of power series over $B/pB$. Assume that all components of $\rho$ and of $\rho'$ have vanishing constant coefficient, and that $t$ and $t'$ are isomorphic in the sense of `Rigidified.IsIsomorphic`: there are pairs of power series $u,v$ over $B$ and an $m \in \mathbb N$ such that $u$ is an $\mathcal O_D$-homomorphism $X \to X'$ and $v$ one $X' \to X$ (law homomorphism of the underlying formal groups, commuting with all $\mathrm{act}\,a$ and with $\varpi$), $v\circ u$ and $u\circ v$ are the identity, and $[p^{m+n'}]_{\overline{X'}}\circ(\bar u\circ\rho)=[p^{m+n}]_{\overline{X'}}\circ\rho'$ over $B/pB$, where $\bar u$ is $u$ reduced modulo $p$ and $\overline{X'}$ denotes `t'.Xbar`, the formal $\mathcal O_D$-module over $B/pB$ attached to $t'$. Then the base changes along $g$ — obtained by pushing $X$, $X'$ forward along $g$, keeping $n$, $n'$, and pushing $\rho$, $\rho'$ forward along the induced map $B/pB \to B'/pB'$ — are again isomorphic in this sense.
--
--   This is the functoriality of the isomorphism relation on rigidified special formal $\mathcal O_D$-modules under base change, the compatibility needed for the moduli problem underlying the Čerednik–Drinfeld uniformisation to be well defined on the category of $B$-algebras. It is used in the construction of the moduli package and the verification of its sheaf property for the Zariski topology, and in the study of isogenies of Cartier quadruples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsIsomorphic_map_ringHom.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsIsomorphic.map_ringHom
    {p : ℕ} [Fact p.Prime] {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B B' : Type u} [CommRing B] [CommRing B'] (g : B →+* B') (t t' : Rigidified p Φ B)
    (hρ : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (h : t.IsIsomorphic t') : (t.map g).IsIsomorphic (t'.map g) := by sorry
