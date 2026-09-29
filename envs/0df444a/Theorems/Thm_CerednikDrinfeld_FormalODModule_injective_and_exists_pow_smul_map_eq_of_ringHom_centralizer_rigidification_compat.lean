-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
-- name    : CerednikDrinfeld.FormalODModule.injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/d5d95602-7599-5d70-8f50-1199d36c7c0f
-- title:
--   Faithfulness and near-fullness of the matrix representation E
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota\colon \mathbb{W}(\mathbb{F}_{p^2}) \to \mathbb{W}(k)$ a ring homomorphism (here `Zp2 p` is $\mathbb{W}(\mathrm{GF}(p^2))$); write $j$ for $\iota$ followed by the quotient map onto $\mathbb{W}(k)/p\mathbb{W}(k)$. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $\mathbb{W}(k)/p\mathbb{W}(k)$, that is, a two-dimensional commutative formal group law $\Phi.F$ with an action of $\mathbb{W}(\mathbb{F}_{p^2})$ by law endomorphisms and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$. Assume: $\Phi$ is special for $j$ (the two eigen-submodules `lieZero` and `lieOne` of the Lie module are complementary and invertible); $\Phi$ has height $4$, i.e. the kernel of the series of $p$ is finite projective of fibre rank $p^4$; and (`hcΦ`) the degree-$0$ and degree-$1$ graded pieces of the Cartier module $M =$ `CartierModule p Φ.F` — where Teichmüller elements act through $j$ composed with the $p^n$-power — are complementary, so that $M$ carries the graded Cartier module data $D$ with Frobenius, Verschiebung, $\varpi$ and the two pieces. Let $r_\Phi\colon \mathbb{Z}_p^2 \to D.\mathrm{NMod}$ be an additive map, $D.\mathrm{NMod}$ being the quotient of $D.M\times D.\Sigma$ by the relation submodule, and assume $r_\Phi$ maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece `etaPiece L _ 0` for every canonical $L$-map $L\colon D.M \to D.\mathrm{NMod}$. Let $E$ be a ring homomorphism from the centralizer of $\{\Phi.\mathrm{actEnd}\,a\}_a \cup \{\Phi.\mathrm{varpiEnd}\}$ into $M_2(\mathbb{Q}_p)$, and assume: every $e$ in this centralizer induces an additive endomorphism $N_e$ of $D.\mathrm{NMod}$ compatible, via `nMk`, with the action of $e$ on $D.M$ and on $D.\Sigma$; and for every such $e$ there is $A \in M_2(\mathbb{Z}_p)$ with $p\,E(e) = A$ in $M_2(\mathbb{Q}_p)$ and $p\,N_e(r_\Phi w) = r_\Phi(Aw)$ for all $w \in \mathbb{Z}_p^2$ and all induced $N_e$. Then $E$ is injective, and there is $m \in \mathbb{N}$ such that every $A \in M_2(\mathbb{Z}_p)$ is of the form $E(e) = p^m A$ for some $e$ in the centralizer.
--
--   This is the faithfulness and near-surjectivity half of the identification $\operatorname{End}^0_{\mathcal{O}_D}(\Phi) = M_2(\mathbb{Q}_p)$ for a special formal $\mathcal{O}_D$-module of height $4$ over $\mathbb{W}(k)/p$, in the form used in Drinfeld's description of the $p$-adic uniformisation: the matrix representation on the degree-$0$ part of the $\eta$-module is injective and its image contains $p^m M_2(\mathbb{Z}_p)$. It feeds the construction of the quasi-isogeny action and the determinant/kernel-degree statement downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat.lean

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

theorem CerednikDrinfeld.FormalODModule.injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat
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
    Function.Injective E ∧
      ∃ m : ℕ, ∀ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), E e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p]) := by sorry
