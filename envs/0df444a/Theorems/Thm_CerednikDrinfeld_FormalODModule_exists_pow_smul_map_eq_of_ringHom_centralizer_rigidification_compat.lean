-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
-- name    : CerednikDrinfeld.FormalODModule.exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/0273d1f4-0f86-5bc3-afc3-3a9d2ac55af6
-- title:
--   Image of E contains p^mM₂(ℤₚ)
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota\colon W(\mathbb{F}_{p^2})\to W(k)$ a ring homomorphism; write $j$ for $\iota$ followed by reduction modulo the ideal $pW(k)$. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $W(k)/pW(k)$, that is, a two-dimensional commutative formal group law $F$ together with an action of $W(\mathbb{F}_{p^2})$ by endomorphisms and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ a=\sigma(a)\circ\varpi$. Assume: $\Phi$ is special for $j$ (the Lie algebra is the direct sum of the eigen-submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$, both invertible); $\Phi$ has height $4$, i.e. the kernel algebra of $[p]$ is finite projective of rank $p^{4}$ at every field-valued point; and the two graded pieces in degrees $0$ and $1$ of the Cartier module of $F$ — the subgroups on which the Teichmüller elements of $\mathbb{F}_{p^2}$ act through $j(\cdot)$ and $j(\cdot)^{p}$ — are complementary, so that the Cartier module of $\Phi$ assembles into graded Cartier module data $D$ with $F$, $V$, $\varpi$ and the two pieces. Given an additive map $r_\Phi\colon \mathbb{Z}_p^{2}\to D.\mathrm{NMod}$ which, for every canonical $L$-map $L$ on $D$, maps $\mathbb{Z}_p^{2}$ bijectively onto the degree-$0$ part $\mathrm{etaPiece}\,L\,0$; a ring homomorphism $E$ from the centralizer of the image of the $W(\mathbb{F}_{p^2})$-action together with $\varpi$ inside $\mathrm{End}(F)$ to $M_2(\mathbb{Q}_p)$; the hypothesis that every $e$ in this centralizer induces an additive endomorphism $N_e$ of $D.\mathrm{NMod}$ compatible with the action of $e$ on $D.M\times D.\Sigma$ through $\mathrm{nMk}$; and the hypothesis that for every such $e$ there is $A\in M_2(\mathbb{Z}_p)$ with $p\,E(e)=A$ in $M_2(\mathbb{Q}_p)$ and with $p\,N_e(r_\Phi(w))=r_\Phi(Aw)$ for all $w\in\mathbb{Z}_p^{2}$ and all $N_e$ satisfying that compatibility. Then there is a natural number $m$ such that every $A\in M_2(\mathbb{Z}_p)$ is of the form $E(e)=p^{m}A$ for some $e$ in the centralizer.
--
--   This is the co-fullness half of the identification $\mathrm{End}^{0}_{\mathcal{O}_D}(\Phi)\cong M_2(\mathbb{Q}_p)$ for a special formal $\mathcal{O}_D$-module of height $4$ over $W(k)/pW(k)$: the image of the matrix representation $E$ on the commutant of the $\mathcal{O}_D$-action contains the lattice $p^{m}M_2(\mathbb{Z}_p)$, so that $E$ becomes surjective after inverting $p$. It is combined with the injectivity of $E$ in [`CerednikDrinfeld.FormalODModule.injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat`](thm.html#CerednikDrinfeld.FormalODModule.injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat), on the way to the Čerednik–Drinfeld description of the formal moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hNe : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))))
    (hE : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p],
        (p : ℚ_[p]) • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) ∧
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p • Ne (rΦ w) = rΦ (A.mulVec w)) :
    ∃ m : ℕ, ∀ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), E e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p]) := by sorry
