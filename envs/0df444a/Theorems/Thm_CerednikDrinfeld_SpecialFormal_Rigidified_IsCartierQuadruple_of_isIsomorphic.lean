-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_of_isIsomorphic
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.of_isIsomorphic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/6c51685d-9359-5980-8546-177d963609a9
-- title:
--   Invariance of the Cartier-quadruple property under isomorphism
-- statement:
--   Fix a prime $p$, a commutative ring $O$ and a ring homomorphism $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $O/pO$ (a commutative formal group law in two variables with an action of $\mathbb{W}(\mathbb{F}_{p^2})$ and a uniformiser endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$). Assume $\Phi$ is special for $\bar\jmath = \iota \bmod p$, i.e. the two eigen-submodules $\mathrm{Lie}^0$, $\mathrm{Lie}^1$ of $\mathrm{Lie}\,\Phi$ are complementary and invertible, and that $\Phi$ has height $4$, i.e. the kernel of $[p]$ has degree $p^4$. Let $h_{c\Phi}$ witness that the graded pieces of degree $0$ and $1$ of the Cartier module of $\Phi$ are complementary, let $D_\Phi$ be the resulting graded Cartier module data, and let $r_\Phi : \mathbb{Z}_p^2 \to (D_\Phi)^{\mathrm{NMod}}$ be an additive map which, for every canonical $L$-map $L$ on $D_\Phi$, maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$. Let $B$ be a noetherian $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, let $\psi : O \to B$ be a ring homomorphism, and let $t, t'$ be rigidified data over $B$ (a formal $O_D$-module, an integer $n$, and a series $\rho$ over $B/pB$), both admissible, i.e. with $X$ special for $\psi\circ\iota$ of height $4$ and $\rho$ an isogeny $\bar\Phi \to \bar X$ of height $4n$. Assume $t$ and $t'$ are isomorphic: there are mutually inverse $O_D$-homomorphisms between $t.X$ and $t'.X$ and an $m$ making the rigidifications agree after composing with $[p^{m+n}]$. Finally let $Q$ be a Drinfeld datum over $B$ for $\mathbb{Q}_p$ with uniformiser $p$. Then if $Q$ is a Cartier quadruple for $t$ — the condition `IsCartierQuadruple`, comprising that $\rho$ is an $O_D$-homomorphism, the existence of $B$-linear isomorphisms of $Q.T_0$, $Q.T_1$ with the Lie eigen-submodules of $t.X$ intertwining $Q.\Pi_0, Q.\Pi_1$ with $\mathrm{Lie}\,\varpi$, and a local description, at each prime of $B$, of the lattices $N_0, N_1$ and of the maps $u_0, u_1$ through $\eta$-sections of graded Cartier data over Zariski-open neighbourhoods, summarised here — then $Q$ is a Cartier quadruple for $t'$ as well.
--
--   Part of the construction of the Čerednik–Drinfeld period map: it shows that the Drinfeld datum attached to an admissible rigidified formal $O_D$-module depends only on the isomorphism class of the latter. It is used in the statement comparing Drinfeld data for isomorphic rigidified data, in the corresponding invariance statement for period values, and in the construction of Cartier quadruples along edge isogenies.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_of_isIsomorphic.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.of_isIsomorphic
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (htt' : t.IsIsomorphic t')
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) :
    t'.IsCartierQuadruple ι hcΦ rΦ ψ Q := by sorry
