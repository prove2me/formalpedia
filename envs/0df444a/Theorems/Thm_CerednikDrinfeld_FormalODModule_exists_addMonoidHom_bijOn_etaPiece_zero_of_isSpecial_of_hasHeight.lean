-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijOn_etaPiece_zero_of_isSpecial_of_hasHeight
-- name    : CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijOn_etaPiece_zero_of_isSpecial_of_hasHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/df37a00f-d9a6-5d27-88f1-f5db1c34feb5
-- title:
--   A canonical ℤₚ²-parametrisation of η_{Φ,0}
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, and a ring homomorphism $\iota\colon \mathrm{Zp2}\,p = W(\mathbb{F}_{p^2}) \to W(k)$; write $j$ for the composite of $\iota$ with the quotient map $W(k) \to W(k)/pW(k)$. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $B = W(k)/pW(k)$, that is, a two-dimensional commutative formal group law $F$ together with an action of $\mathrm{Zp2}\,p$ by endomorphism series and a series $\varpi$ satisfying $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$. Assume: $\Phi$ is special with respect to $j$, i.e. the Lie pieces $\mathrm{lieZero}\,j$ and $\mathrm{lieOne}\,j$ are complementary and both invertible $B$-modules; $\Phi$ has height $4$, i.e. $\mathrm{act}(p)$ has kernel of degree $p^4$; and the graded pieces of the Cartier module $\mathrm{CartierModule}\,p\,F$ in degrees $0$ and $1$ — the subgroups of elements $f$ with $\mathrm{endAct}(\mathrm{actEnd}(\tau c))f = j(\tau c)^{p^{n}} \cdot f$ for all $c \in \mathbb{F}_{p^2}$, $\tau$ the Teichmüller lift — are complementary (hypothesis $h_{c\Phi}$). Let $D = \Phi.\mathrm{toGradedCartierModuleData}\,j\,h_{c\Phi}$ be the associated graded Cartier module datum, with $D.M = \mathrm{CartierModule}\,p\,F$ and $D.\mathrm{NMod}$ the quotient of $D.M \times D.\Sigma$ by the relation $D.\mathrm{nRel}$. The conclusion: there is an additive homomorphism $r_\Phi \colon (\mathrm{Fin}\,2 \to \mathbb{Z}_p) \to D.\mathrm{NMod}$ such that for *every* additive map $L\colon D.M \to D.\mathrm{NMod}$ that is a canonical $L$-map (a Cartier $L$-map admitting a lift from a special graded Cartier module datum along a surjection), $r_\Phi$ maps the whole of $(\mathrm{Fin}\,2 \to \mathbb{Z}_p)$ bijectively onto $\mathrm{etaPiece}\,L\,\dots\,0 = D.\mathrm{eta}\,L \sqcap D.\mathrm{nPiece}\,0$.
--
--   This is the rigidification step in the Čerednik–Drinfeld uniformisation: at a geometric point the degree-zero part of the $\eta$-subgroup attached to a special formal $\mathcal{O}_D$-module of height $4$ is free of rank $2$ over $\mathbb{Z}_p$, and a single parametrisation works simultaneously for all canonical $L$-maps. It feeds the construction of Drinfeld data and the base-change criterion for rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijOn_etaPiece_zero_of_isSpecial_of_hasHeight.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijOn_etaPiece_zero_of_isSpecial_of_hasHeight
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1)) :
    ∃ rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
        (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
        Set.BijOn rΦ Set.univ
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _) := by sorry
