-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/bcafbb42-4525-5c2c-9162-2d5a0c67dceb
-- title:
--   Admissibility of a composed rigidification over the edge-chart ring
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, write $\mathbb Z_{p^2}=W(\mathbb F_{p^2})$, and let $\bar W := W(k)/pW(k)$ and let $E$ denote `EdgeFamily.edgeRingCharP p` applied to $\bar W$, the localisation away from `FormalOmega.edgeQuot.discr` of the edge chart ring of $\bar W$ at parameter $0$ and $p$. Let $\iota:\mathbb Z_{p^2}\to W(k)$ be a ring homomorphism, $\Phi$ a formal $\mathcal O_D$-module over $\bar W$ (a commutative two-dimensional formal group law together with an action of $\mathbb Z_{p^2}$ by law endomorphisms and a law endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\mathrm{Frob}\,a]\circ\varpi$), and $X$ such a module over $E$. Write $\psi_E:W(k)\to E$ for the reduction $W(k)\to\bar W$ followed by the structure map $\bar W\to E$. Assume: $X$ is special for the structure homomorphism $\psi_E\circ\iota$, that is, its zero- and one-eigenspace submodules `lieZero` and `lieOne` of its Lie module are complementary and both invertible; $X$ has height $4$, i.e. $[p]$ on $X$ has kernel algebra finite and projective over $E$ of rank $p^4$ at every field-valued point. Let $f_0:E\to\bar W$ be a ring homomorphism, $m\in\mathbb N$, and let $\rho_0$ be a system of two power series over $\bar W$ which is an $\mathcal O_D$-linear isogeny $\Phi\to X\otimes_{f_0}\bar W$ with kernel of degree $p^{4m}$, and $\rho_1$ a system over $E$ which is an $\mathcal O_D$-linear isogeny $(X\otimes_{f_0}\bar W)\otimes_{\bar W}E\to X$ with kernel of degree $p^{4}$. Then the rigidified datum consisting of $X$, the integer $m+1$ and the composite of the base change of $\rho_0$ along $\bar W\to E\to E/pE$ followed by the reduction of $\rho_1$ modulo $p$ is admissible for $(\iota,\psi_E)$: $X$ is special and of height $4$ as above, and that composite is an $\mathcal O_D$-linear isogeny from the base change of $\Phi$ along the reduction of $\psi_E$ to $X\otimes_E E/pE$ with kernel of degree $p^{4(m+1)}$.
--
--   This is the verification that the rigidifications produced at an edge of the Bruhat–Tits tree satisfy the admissibility condition in the Drinfeld moduli description of $p$-adic uniformisation, in the form used by Boutot–Carayol: a node isogeny of height $4m$ followed by the explicit edge isogeny of height $4$ yields a level-$(m+1)$ rigidification. It supplies the admissibility input to the statements constructing Cartier quadruples and $\eta$-sections for edge isogenies over the characteristic-$p$ edge chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)
    (f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
    (ρ₁ : Series (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (hρ₁ : FormalODModule.IsIsogenyOfHeight ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X ρ₁ 4) :
    (Rigidified.mk (Φ := Φ) X (m + 1)
      ((ρ₁.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp
        (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).IsAdmissible ι
      ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) := by sorry
