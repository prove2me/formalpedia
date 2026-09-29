-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_of_isBaseChangeAlong_of_comp_eq
-- name    : CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/e24d3fca-7089-5652-bc09-d8f7ae0e43e2
-- title:
--   Canonical L-maps persist under base change, label-free form
-- statement:
--   Fix a prime $p$ and commutative rings $B$, $B'$, together with ring homomorphisms $j : \mathbb{W}(\mathbb{F}_{p^2}) \to B$ and $j' : \mathbb{W}(\mathbb{F}_{p^2}) \to B'$ (where `Zp2 p` is the Witt ring of the field of $p^2$ elements) and a ring homomorphism $\varphi : B \to B'$ with $\varphi \circ j = j'$. Let $D$ be graded Cartier module data over $(B,j)$ and $D'$ over $(B',j')$, each assumed special, i.e. possessing a homogeneous $V$-basis $\gamma : \mathrm{Fin}\,2 \to M$ and being $V$-adically complete in the sense of `IsVAdicallyComplete`. Let $f : D.M \to D'.M$ be additive and a base change along $\varphi$ in the sense of `IsBaseChangeAlong'`: it is semilinear for $\mathbb{W}(\varphi)$, commutes with $F$, $V$ and $\varpi$, carries each graded piece into the corresponding piece of $D'$, and maps some homogeneous $V$-basis of $D$ to a homogeneous $V$-basis of $D'$. Finally let $L : D.M \to D.\mathrm{NMod}$ be a canonical $L$-map, that is, a Cartier $L$-map ($\sigma$-semilinear, with $L \circ V =$ the class of $(\varpi x, 0)$ and $\lambda \circ L = F$) admitting a lift over a surjection $S \to B$ from a ring without $p$-torsion carrying special data and a Cartier $L$-map compatible with $L$ through `nMap`. The conclusion is the bare existence of some canonical $L$-map $L' : D'.M \to D'.\mathrm{NMod}$; no compatibility of $L'$ with $L$ along $f$ is asserted.
--
--   This is the untyped, or label-free, packaging of the statement that the canonicity of an $L$-map on special graded Cartier module data is inherited by a base change, the structure map of the target being given as an independent parameter $j'$ constrained only by $\varphi \circ j = j'$. It is used in the construction of Cartier quadruples attached to special formal $\mathcal{O}_D$-modules, in the base-change compatibility of the map $u$ and in the comparison of the $N$-modules under a morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_of_isBaseChangeAlong_of_comp_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_of_isBaseChangeAlong_of_comp_eq
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (j' : CerednikDrinfeld.Zp2 p →+* B') (φ : B →+* B') (hj : φ.comp j = j')
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) :
    ∃ L' : D'.M →+ D'.NMod, D'.IsCanonicalLMap L' := by sorry
