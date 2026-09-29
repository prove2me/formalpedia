-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_nsmul_rigidNum_mem_eta
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.nsmul_rigidNum_mem_eta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/1b357d9a-708c-57b0-ba55-f844b104b0c5
-- title:
--   p times the rigidification numerator lies in η(̄ L)
-- statement:
--   Fix a prime $p$ and a commutative ring $O$ with a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to O$, and let $\Phi$ be a formal $\mathcal{O}_D$-module over $O/pO$, i.e. a two-dimensional commutative formal group law together with an action of $W(\mathbb{F}_{p^2})$ and a series $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$. Write $\bar\iota$ for $\iota$ followed by reduction mod $p$. Assume the two graded pieces of the Cartier module of $\Phi$ in degrees $0$ and $1$ for $\bar\iota$ — the eigenspaces on which the Teichmüller action of $c \in \mathbb{F}_{p^2}$ is the homothety by $\bar\iota(c)^{p^n}$ — are complementary ($hc\Phi$), so that the Cartier module with its $F$, $V$, $\varpi$ and this decomposition form graded Cartier module data. Let $r_\Phi : \mathbb{Z}_p^{2} \to N(M_\Phi)$ be additive, let $L_\Phi$ be an additive map $M_\Phi \to N(M_\Phi)$ which is a Cartier $L$-map (semilinear for the Frobenius of Witt vectors, sending $V x$ to the class of $(\varpi x, 0)$, and lifting $F$ through $\lambda$), and assume every value of $r_\Phi$ lies in $\eta(L_\Phi)$, the kernel of $\phi_{L_\Phi} - \mathrm{id}$ on $N(M_\Phi)$. Let $\psi : O \to B$ be a ring homomorphism and $t = (X, n, \rho)$ a rigidified object over $B$ whose $\rho$ is an $\mathcal{O}_D$-homomorphism $\bar\Phi_\psi \to \bar X$ ($hOD$), and let $g : B \to S$ be a ring homomorphism. Assume the corresponding degree-$0$/degree-$1$ pieces are complementary for $\bar X_S$ over $S/pS$ ($hcb$) and for $\bar\Phi_S$ ($hc\Phi g$). Finally let $\bar L$ be any Cartier $L$-map for the graded Cartier module data of $\bar X_S$. Then for every $w \in \mathbb{Z}_p^{2}$, $p$ times the rigidification numerator $r(w)$ — the image of $r_\Phi(w)$ under the $N$-functoriality maps induced by base change $\bar\Phi \to \bar\Phi_S$ and by $\rho$ — lies in $\eta(\bar L)$.
--
--   This is the statement that $\eta$ is functorial only up to a factor of $p$: the Cartier-module period attached to a rigidification of a special formal $\mathcal{O}_D$-module becomes a $\phi_{\bar L}$-fixed element of the reduced module after multiplication by $p$, with no compatibility assumed between $L_\Phi$ and $\bar L$. It is the input used in the lower bound for the $\eta$-lattice, and is cited in the construction of $\eta$-sections and the identification of $\eta$-stalks with Drinfeld lattices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_nsmul_rigidNum_mem_eta.lean

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

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.nsmul_rigidNum_mem_eta
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (LΦ : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCartierLMap LΦ)
    (hrΦ : ∀ w, rΦ w ∈ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).eta LΦ hLΦ.map_verschiebung)
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (Lb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).M →+
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod)
    (hLb : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).IsCartierLMap Lb)
    (w : Fin 2 → ℤ_[p]) :
    p • Rigidified.rigidNum ι hcΦ rΦ ψ t hOD g hcb hcΦg w ∈
      ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).eta Lb hLb.map_verschiebung := by sorry
