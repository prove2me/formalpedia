-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_map_nMap_of_isBaseChangeAlong
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_map_nMap_of_isBaseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/5a5330f9-ab90-52e4-a964-fccc3cfa53c8
-- title:
--   Base change of η-sections with rigidified coordinates
-- statement:
--   Fix a prime $p$, a commutative ring $O$ and a ring map $\iota:\mathbb{W}(\mathbb{F}_{p^2})\to O$, and let $\Phi$ be a formal $O_D$-module over $O/(p)$ whose degree-$0$ and degree-$1$ graded pieces of its Cartier module with respect to $\bar\iota=\iota$ followed by reduction mod $p$ are complementary (hypothesis $h_{c\Phi}$), together with an additive map $r_\Phi:\mathbb{Z}_p^2\to N(\Phi)$ into the associated $N$-module. Let $\psi:O\to B$, $\psi':O\to B'$, $f:B\to B'$ with $f\circ\psi=\psi'$, let $t=(X,n,\rho)$ be a rigidified datum over $B$, and assume $\rho$ and its image under $f$ are $O_D$-law homomorphisms ($h_{OD}$, $h_{OD}'$). Let $g:B\to S$, $g':B'\to S'$ and $e:S\to S'$ satisfy $g'\circ f=e\circ g$, and assume the six complementarity conditions $h_c,h_{cb},h_{c\Phi g}$ over $S$ and $h_c',h_{cb}',h_{c\Phi g}'$ over $S'$, which turn the Cartier modules of $X_S$, $\bar X_S$, $\bar\Phi_S$ and of their primed analogues into graded Cartier module data. Let $bc$ be an additive map between the Cartier modules of $X_S$ and of $(t\otimes B')_{S'}$ which is a base change along $e$ in the sense of `IsBaseChangeAlong'`: it is $\mathbb{W}(e)$-semilinear, commutes with Frobenius, Verschiebung and $\varpi$, preserves the two graded pieces, and carries some homogeneous $V$-basis to a homogeneous $V$-basis. Let $L$, $L'$ be canonical $L$-maps on the two data with $L'\circ bc = N(bc)\circ L$, and let $\overline{bc}$ be an additive map on the reduced $N$-modules such that the reduction maps satisfy $\overline{\eta}_{t\otimes B'}\circ N(bc)=\overline{bc}\circ\overline{\eta}_t$ and the rigidification numerators satisfy $\mathrm{rigidNum}_{t\otimes B'}=\overline{bc}\circ\mathrm{rigidNum}_t$. Then for every $i\in\{0,1\}$, every $z$ in the $N$-module over $S$ and every $v\in\mathbb{Q}_p^2$: if $z$ is an $\eta$-section of index $i$ with coordinates $v$ for $t$ — that is, $z$ lies in $\eta\cap N$-piece $i$ and the reduction of $\nu_\varpi^i z$ stands in the lattice relation of level $n$ with $p^i v$ via $\mathrm{rigidNum}_t$ — then $N(bc)(z)$ is an $\eta$-section of index $i$ with the same coordinates $v$ for $t\otimes_B B'$ over $S'$.
--
--   This is the functoriality in the base of the notion of an $\eta$-section with rigidified coordinates, the local datum used in the Čerednik–Drinfeld description of special formal $O_D$-modules. It feeds the base-change compatibility of the Cartier quadruple attached to a rigidified module, being used in the treatment of `IsCartierQuadrupleVia` and in the bound on the lattice $N$ under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_map_nMap_of_isBaseChangeAlong.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_map_nMap_of_isBaseChangeAlong
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ')
    (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hOD' : FormalODModule.IsODHom ((t.map f).Φbar ψ') (t.map f).Xbar (t.map f).ρ)
    {S S' : Type} [CommRing S] [CommRing S'] (g : B →+* S) (g' : B' →+* S') (e : S →+* S')
    (hge : g'.comp f = e.comp g)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (hc' : (t.map f).IsGradedS ι ψ' g') (hcb' : (t.map f).IsGradedSbar ι ψ' g')
    (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' g')
    (bc : MvFormalGroup.CartierModule p (t.XS g).F →+ MvFormalGroup.CartierModule p ((t.map f).XS g').F)
    (hbc : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' e ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc)
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+ ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (L' : (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc').M →+ (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc').NMod) (hL' : (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc').IsCanonicalLMap L')
    (hLL' : ∀ x, L' (bc x) = ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 (L x))
    (bcbar : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod →+ (((t.map (f : B →+* B')).XbarS g').toGradedCartierModuleData (Rigidified.jSbar ι ψ' g') hcb').NMod)
    (hred : ∀ z, (t.map f).etaRed ι ψ' g' hc' hcb' (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 z) =
      bcbar (t.etaRed ι ψ g hc hcb z))
    (hrig : ∀ w, (t.map f).rigidNum ι hcΦ rΦ ψ' hOD' g' hcb' hcΦg' w = bcbar (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg w))
    (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (v : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v) :
    (t.map f).IsEtaSection ι hcΦ rΦ ψ' hOD' g' hc' hcb' hcΦg' L' hL' i
      (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 z) v := by sorry
