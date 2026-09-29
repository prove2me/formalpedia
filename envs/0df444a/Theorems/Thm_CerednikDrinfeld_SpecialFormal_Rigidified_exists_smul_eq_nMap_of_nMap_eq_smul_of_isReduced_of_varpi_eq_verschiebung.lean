-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_verschiebung
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_verschiebung
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a91cb3d6-2b60-5a73-898f-f5d93aa66368
-- title:
--   Zariski-local p-divisibility of ηⱼ at a critical index
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring homomorphism $\iota \colon \mathrm{Zp2}\,p \to O$ (where $\mathrm{Zp2}\,p$ denotes the Witt vectors of the field with $p^2$ elements), a formal $O_D$-module $\Phi$ over $O/pO$, a Noetherian commutative $\mathbb{Z}_p$-algebra $B$, a ring homomorphism $\psi \colon O \to B$ with $p$ nilpotent in $B$, and a rigidified object $t$ over $B$ (a formal $O_D$-module $t.X$ over $B$, an integer $n$, and a system of power series $\rho$ modulo $p$) which is admissible for $\iota,\psi$, i.e. $t.X$ is special for the structure map $\psi \circ \iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from $\Phi$ base-changed to $B/pB$ to $t.X$ modulo $p$. Let $g \colon B \to S$ be a homomorphism into a reduced Noetherian ring $S$ with $p = 0$ in $S$, and suppose `hc` that the graded pieces of degrees $0$ and $1$ of the Cartier module of the formal module `t.XS g` over $S$, taken with respect to the structure homomorphism `jS` $\iota\,\psi\,g$, are complementary submodules; write $D$ for the resulting graded Cartier module datum, with its Frobenius, Verschiebung, its $\varpi$-operator and its two pieces. Let $L \colon D.M \to D.\mathrm{NMod}$ be a canonical $L$-map, let $j \in \{0,1\}$, let $\gamma$ be a homogeneous $V$-basis of $D$ (each $\gamma_i$ in the $i$-th piece, and every element uniquely of the form $\sum_i [c_i]\gamma_i + V m$), and assume the criticality condition $\varpi(\gamma_j) = V x_j$ for some $x_j$. Let $z$ lie in the $j$-th graded piece $\mathrm{etaPiece}\,L\,j$ of $\eta$. Let $x$ be a prime of $S$ and $k \colon S \to K$ a homomorphism into an algebraically closed field with kernel the prime of $x$, with a corresponding grading `hc'` and a canonical $L'$ over $K$, the identification `hXh` of the base change along $k$ of the formal group of `t.XS g` with that of `t.XS (k.comp g)`, and the hypotheses that the associated map `baseChangeEq` commutes with Verschiebung and with $\varpi$. Assume finally that the induced map `nMap` on $N$-modules sends $z$ to $p\,y$ for some $y$ in the $j$-th graded piece of $\eta$ for $L'$ over $K$. Then there exists $f_0 \in S$ not in the prime of $x$, together with a grading `hc₀` and a canonical $L_0$ over the localisation $S[1/f_0]$, an identification `hXr` of formal groups along $S \to S[1/f_0]$ whose `baseChangeEq` commutes with Verschiebung and with $\varpi$, and an element $z_0$ in the $j$-th graded piece of $\eta$ for $L_0$ such that $p\,z_0$ equals the image of $z$ under the induced map on $N$-modules over $S[1/f_0]$.
--
--   This is the spreading-out step in the Čerednik–Drinfel'd comparison of special formal $O_D$-modules with Cartier module data: $p$-divisibility of a section of $\eta_j$ observed at one geometric point of a reduced stratum on which the index $j$ is critical is propagated to a Zariski neighbourhood of that point. It is used by the two subsequent divisibility-descent lemmas, which treat the remaining shape of the $\varpi$-equation and combine the strata.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_verschiebung.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_nMap_eq_smul_of_isReduced_of_varpi_eq_verschiebung
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsReduced S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2) (γ : Fin 2 → ((t.XS g).toGradedCartierModuleData _ hc).M) (hγ : ((t.XS g).toGradedCartierModuleData _ hc).IsHomogeneousVBasis γ)
    (xj : ((t.XS g).toGradedCartierModuleData _ hc).M) (hcrit : ((t.XS g).toGradedCartierModuleData _ hc).varpi (γ j) = ((t.XS g).toGradedCartierModuleData _ hc).verschiebung xj)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    {K : Type} [Field K] [IsAlgClosed K] (k : S →+* K) (hk : RingHom.ker k = x.asIdeal)
    (hc' : t.IsGradedS ι ψ (k.comp g))
    (L' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').M →+ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').NMod) (hL' : ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').IsCanonicalLMap L')
    (hXh : (t.XS g).F.map k = (t.XS (k.comp g)).F)
    (hbcV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hbcPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXh (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXh m))
    (hdiv : ∃ y ∈ ((t.XS (k.comp g)).toGradedCartierModuleData _ hc').etaPiece L' hL'.isCartierLMap.map_verschiebung j,
      ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS (k.comp g)).toGradedCartierModuleData _ hc') (MvFormalGroup.CartierModule.baseChangeEq _ hXh) hbcV hbcPi z = p • y) :
    ∃ (f₀ : S) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
      (L₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by sorry
