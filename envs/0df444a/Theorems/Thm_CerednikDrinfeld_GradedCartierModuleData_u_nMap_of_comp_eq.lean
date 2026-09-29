-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_u_nMap_of_comp_eq
-- name    : CerednikDrinfeld.GradedCartierModuleData.u_nMap_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/549bbc1c-bbc2-54bc-81c9-e5022d33acf1
-- title:
--   Base change compatibility of u on η(L)
-- statement:
--   Fix a prime $p$, commutative rings $B$ and $B'$, and ring homomorphisms $j\colon \mathbb{W}(\mathbb{F}_{p^2})\to B$ and $j'\colon \mathbb{W}(\mathbb{F}_{p^2})\to B'$ (here [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) is the ring of Witt vectors of the field with $p^2$ elements), together with graded Cartier module data $D$ over $(p,B,j)$ and $D'$ over $(p,B',j')$; each such datum consists of a module over the Witt vectors of the base ring equipped with additive maps $F$, $V$, a linear map $\varpi$ and a decomposition into two complementary pieces permuted by $F$, $V$, $\varpi$, subject to the usual Cartier relations. Let $bc\colon D.M \to D'.M$ be an additive map commuting with the Verschiebungen (`hV`) and with the $\varpi$'s (`hPi`), and let $L\colon D.M \to D.\mathrm{NMod}$ and $L'\colon D'.M \to D'.\mathrm{NMod}$ be additive maps into the respective quotients $(M\times M^{\sigma})/\langle (Vm, -\varpi m)\rangle$ satisfying $L(Vx)=\mathrm{nMk}(\varpi x,0)$ and likewise for $L'$, and assume $L'(bc\,x) = \mathrm{nMap}(bc)(L\,x)$ for all $x$, where $\mathrm{nMap}(bc)$ is the map of quotients induced by $bc$ on both coordinates. Then for every $z$ in `D.eta L hLV`, the subgroup of $D.\mathrm{NMod}$ on which `D.phi L hLV` is the identity, the element $\mathrm{nMap}(bc)(z)$ lies in `D'.eta L' hLV'`; moreover, for every $m\in D.M$ and every proof $hz'$ of that membership, if the class of $m$ in $D.M/V(D.M)$ equals `D.u L hLV ⟨z, hz⟩`, then the class of $bc\,m$ in $D'.M/V(D'.M)$ equals `D'.u L' hLV' ⟨nMap(bc) z, hz'⟩`. The membership proof $hz'$ is quantified over in the second clause, so the conclusion holds for any such proof.
--
--   This is the base-change compatibility of the map $u(L)\colon \eta(L)\to M/VM$ attached to graded Cartier module data, as used in the Čerednik–Drinfeld theory of special formal $\mathcal{O}_D$-modules in the style of Boutot–Carayol. It is invoked by [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.u_baseChange) and by [`CerednikDrinfeld.SpecialFormal.Rigidified.nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.nMap_bcPhi_apply_mem_etaPiece_zero_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_u_nMap_of_comp_eq.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.u_nMap_of_comp_eq
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B'] {j : CerednikDrinfeld.Zp2 p →+* B}
    {j' : CerednikDrinfeld.Zp2 p →+* B'}
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (D' : CerednikDrinfeld.GradedCartierModuleData p B' j')
    (bc : D.M →+ D'.M)
    (hV : ∀ x, bc (D.verschiebung x) = D'.verschiebung (bc x)) (hPi : ∀ x, bc (D.varpi x) = D'.varpi (bc x))
    (L : D.M →+ D.NMod) (hLV : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hLV' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ x, L' (bc x) = D.nMap D' bc hV hPi (L x))
    (z : D.NMod) (hz : z ∈ D.eta L hLV) :
    D.nMap D' bc hV hPi z ∈ D'.eta L' hLV' ∧
      ∀ (m : D.M) (hz' : D.nMap D' bc hV hPi z ∈ D'.eta L' hLV'),
        D.vRange.mkQ m = D.u L hLV ⟨z, hz⟩ →
        D'.vRange.mkQ (bc m) = D'.u L' hLV' ⟨D.nMap D' bc hV hPi z, hz'⟩ := by sorry
