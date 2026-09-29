-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_of_isODHom
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_nMap_of_isODHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/e152b96a-9c55-56b2-b2ea-b9561ab5b129
-- title:
--   Transport of η-sections along an isomorphism of rigidified modules
-- statement:
--   Fix a prime $p$, a commutative ring $O$ and a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to O$, where `Zp2 p` denotes $W(\mathbb{F}_{p^2})$. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $O/pO$ (a commutative two-dimensional formal group law with a $W(\mathbb{F}_{p^2})$-action and a series $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$), let `hcΦ` assert that the graded pieces in degrees $0$ and $1$ of the Cartier module of $\Phi$ relative to $\bar\jmath = \iota$ followed by reduction mod $p$ are complementary, and let $r_\Phi$ be an additive map from $\mathbb{Z}_p^2$ to the $N$-module of the resulting graded Cartier module data. Let $\psi : O \to B$ be a ring homomorphism, and let $t,t'$ be rigidified data over $B$, each consisting of a formal $\mathcal{O}_D$-module $X$, a natural number $n$ and a series $\rho$ over $B/pB$. Assume given series $u,w$ over $B$ that are homomorphisms $t.X \to t'.X$ and $t'.X \to t.X$ of formal $\mathcal{O}_D$-modules and are mutually inverse under composition, a natural number $m_0$ with $[p^{m_0+t'.n}]\circ(\bar u\circ t.\rho) = [p^{m_0+t.n}]\circ t'.\rho$ on $t'.\bar X$, and that $t.\rho$, $t'.\rho$ are homomorphisms of formal $\mathcal{O}_D$-modules from $\Phi$ base-changed along $\psi$ to $t.\bar X$, $t'.\bar X$ respectively. Let $g : B \to S$ be a ring homomorphism, with complementarity hypotheses `hc`, `hcb`, `hc'`, `hcb'`, `hcΦg` for the degree-$0$ and degree-$1$ graded pieces of the Cartier modules of `t.XS g`, `t.XbarS g`, `t'.XS g`, `t'.XbarS g` and of $\Phi$ base-changed to $S/pS$, relative to the corresponding maps $j$. Let $f_u$ be an additive map from the Cartier module of `t.XS g` to that of `t'.XS g`, equal to the map induced by the homomorphism of formal groups obtained from $u$ by base change along $g$, and assume $f_u$ commutes with Verschiebung and with $\varpi$ on the graded Cartier module data. Let $L$, $L'$ be canonical $L$-maps for the graded Cartier module data of `t.XS g` and `t'.XS g`, satisfying $L'\circ f_u = N(f_u)\circ L$, where $N(f_u)$ is the induced map of $N$-modules. Then for every $i \in \{0,1\}$, every $z$ in the $N$-module of `t.XS g` and every $v \in \mathbb{Q}_p^2$, if $z$ is an $\eta$-section for $t$ with coordinates $v$, that is, $z$ lies in the `etaPiece` of $L$ in degree $i$ and the image of $\Pi^i z$ under the reduction map `etaRed` satisfies the lattice relation in level $t.n$ with respect to `rigidNum` and $p^i v$ (there are $m,k \in \mathbb{N}$ and $w \in \mathbb{Z}_p^2$ with $p^m\cdot p^i v = w$ in $\mathbb{Q}_p^2$ and $p^k\cdot r(w) = p^{k+t.n+m}$ times that image), then $N(f_u)z$ is an $\eta$-section for $t'$ in the same degree $i$ and with the same coordinate vector $v$.
--
--   This is the statement that the $\eta$-sections with rigidified $p$-adic coordinates, attached to a rigidified formal $\mathcal{O}_D$-module via its graded Cartier module, are carried to one another, with unchanged coordinates, by an isomorphism of rigidified data compatible with the rigidifications up to a common power of $p$. It is used to show that the Cartier quadruple attached to such data depends only on its isomorphism class, and in the construction of the linear part of a via-map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_nMap_of_isODHom.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
  MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_nMap_of_isODHom
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B)
    (t t' : Rigidified p Φ B)
    (us ws : Series B) (hu : FormalODModule.IsODHom t.X t'.X us) (hw : FormalODModule.IsODHom t'.X t.X ws)
    (hwu : ws.comp us = Series.id B) (huw : us.comp ws = Series.id B)
    (m₀ : ℕ)
    (hρ : (t'.Xbar.act ((p : Zp2 p) ^ (m₀ + t'.n))).comp
        ((us.map (Ideal.Quotient.mk (pIdeal p B))).comp t.ρ) =
      (t'.Xbar.act ((p : Zp2 p) ^ (m₀ + t.n))).comp t'.ρ)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hOD' : FormalODModule.IsODHom (t'.Φbar ψ) t'.Xbar t'.ρ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g)
    (hc' : t'.IsGradedS ι ψ g) (hcb' : t'.IsGradedSbar ι ψ g)
    (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (fu : CartierModule p (t.XS g).F →+ CartierModule p (t'.XS g).F)
    (hfu : fu = CartierModule.map ((hu.1.map g).toHom : MvFormalGroup.Hom (t.XS g).F (t'.XS g).F))
    (hfuV : ∀ x, fu (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).verschiebung x) =
      ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').verschiebung (fu x))
    (hfuPi : ∀ x, fu (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).varpi x) =
      ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').varpi (fu x))
    (L : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).M →+
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod)
    (hL : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).IsCanonicalLMap L)
    (L' : ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').M →+
      ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').NMod)
    (hL' : ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc').IsCanonicalLMap L')
    (hLL' : ∀ x, L' (fu x) =
      ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap
        ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc') fu hfuV hfuPi (L x))
    (i : Fin 2) (z : ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).NMod) (v : Fin 2 → ℚ_[p])
    (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD g hc hcb hcΦg L hL i z v) :
    t'.IsEtaSection ι hcΦ rΦ ψ hOD' g hc' hcb' hcΦg L' hL' i
      (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap
        ((t'.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc') fu hfuV hfuPi z) v := by sorry
