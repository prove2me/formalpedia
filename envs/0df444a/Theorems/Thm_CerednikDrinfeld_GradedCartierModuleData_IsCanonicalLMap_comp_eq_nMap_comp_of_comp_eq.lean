-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_comp_eq
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/281699ff-c9b4-5099-b60a-5bbc9124e55d
-- title:
--   Naturality of the canonical L-map under base change
-- statement:
--   Fix a prime $p$, commutative rings $B$, $B'$, ring homomorphisms $j \colon \mathbb{W}(\mathbb{F}_{p^2}) \to B$ and $j' \colon \mathbb{W}(\mathbb{F}_{p^2}) \to B'$ (where `Zp2 p` is the Witt vectors of the field with $p^2$ elements), and a ring homomorphism $\varphi \colon B \to B'$ with $\varphi \circ j = j'$, assuming $p$ nilpotent in $B$ and in $B'$. Let $D$ be graded Cartier module data over $(B,j)$ and $D'$ such data over $(B',j')$ — that is, modules over the Witt vectors carrying $F$, $V$, $\varpi$ with the usual Cartier relations and a decomposition into two pieces permuted by these operators — and assume both are special, i.e. each admits a homogeneous $V$-basis indexed by `Fin 2` and is $V$-adically complete. Let $f \colon D.M \to D'.M$ be an additive map which is a base change along $\varphi$ in the label-free sense: it is semilinear for `WittVector.map φ`, commutes with $F$, $V$ and $\varpi$, preserves the two graded pieces, and carries some homogeneous $V$-basis of $D$ to a homogeneous $V$-basis of $D'$. Let $L \colon D.M \to D.\mathrm{NMod}$ and $L' \colon D'.M \to D'.\mathrm{NMod}$ be canonical $L$-maps, i.e. each is a Cartier $L$-map admitting a lift along a surjection from a ring with no $p$-torsion carrying special graded Cartier module data, a base change to it and a Cartier $L$-map compatible with $L$ via `nMap`. The conclusion is that for every $x \in D.M$ one has $L'(f x) = (D.\mathrm{nMap}\,D'\,f)(L x)$, where `nMap` is the map on the quotients $\mathrm{NMod} = (M \times \Sigma)/\mathrm{nRel}$ induced by $f$ on both factors, using the compatibility of $f$ with $V$ and with $\varpi$.
--
--   This records the naturality of the canonical $L$-map in the Cartier-theoretic description of special formal $\mathcal{O}_D$-modules underlying the Čerednik–Drinfeld uniformisation: base change of the module datum commutes with passage to the associated $N$-module. It is the form of the naturality statement in which the $\mathbb{Z}_{p^2}$-labelling of the target is only required to agree with $\varphi \circ j$ propositionally, so that it applies to data whose structure map arises from a localisation; it is used in the study of Cartier quadruples and their rigidifications.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_comp_eq_nMap_comp_of_comp_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.comp_eq_nMap_comp_of_comp_eq
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (j' : CerednikDrinfeld.Zp2 p →+* B') (φ : B →+* B') (hj : φ.comp j = j')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L') :
    ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x) := by sorry
