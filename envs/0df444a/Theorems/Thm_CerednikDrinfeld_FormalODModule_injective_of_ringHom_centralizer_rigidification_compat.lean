-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_injective_of_ringHom_centralizer_rigidification_compat
-- name    : CerednikDrinfeld.FormalODModule.injective_of_ringHom_centralizer_rigidification_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/bfe241c8-8dad-563c-8ed7-fad423223fa8
-- title:
--   Faithfulness of a rigidification-compatible matrix representation of End(Φ)
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, and let $\iota : W(\mathbb F_{p^2}) \to W(k)$ be a ring homomorphism, with $j$ denoting $\iota$ followed by reduction modulo the ideal $(p)$ of $W(k)$. Let $\Phi$ be a formal $\mathcal O_D$-module over $W(k)/p$, that is, a commutative two-dimensional formal group law $\Phi.F$ equipped with an action of $W(\mathbb F_{p^2})$ by endomorphisms and an endomorphism $\Phi.\mathrm{varpiEnd}$ whose square is multiplication by $p$ and which twists the action by Frobenius. Assume: $\Phi$ is special for $j$, i.e. the $j$-eigenspace $\mathrm{lieZero}$ and the $j\circ\mathrm{Frob}$-eigenspace $\mathrm{lieOne}$ of the Lie module are complementary and both invertible; $\Phi$ has height $4$, i.e. the kernel algebra of multiplication by $p$ is finite projective of fibrewise rank $p^4$; and the graded pieces in degrees $0$ and $1$ of the Cartier module of $\Phi.F$ (the subgroups on which the Teichmüller part of the action is homothety by $j(\cdot)^{p^n}$) are complementary, say via $h_{c\Phi}$. Write $D$ for the graded Cartier module data $\Phi.\mathrm{toGradedCartierModuleData}\ j\ h_{c\Phi}$, whose underlying module is the Cartier module of $\Phi.F$ with its Frobenius, Verschiebung, the action of $\Phi.\mathrm{varpiEnd}$ and the two graded pieces, and let $D.\mathrm{NMod}$ be the quotient of $D.M \times D.\mathrm{Sigma}$ by the relation submodule, with quotient map $D.\mathrm{nMk}$. Let $r_\Phi : \mathbb Z_p^2 \to D.\mathrm{NMod}$ be an additive map which, for every canonical $L$-map $L : D.M \to D.\mathrm{NMod}$ (a Cartier $L$-map, Frobenius-semilinear with $L(Vx) = \mathrm{nMk}(\varpi x, 0)$ and $\lambda \circ L = F$, admitting a lift over a surjective base with $p$-torsion-free source carrying a special Cartier module), maps the whole of $\mathbb Z_p^2$ bijectively onto $D.\mathrm{etaPiece}\ L\ \cdot\ 0$, the intersection of the subgroup $D.\mathrm{eta}\ L$ with the degree-$0$ part $D.\mathrm{nPiece}\ 0$. Let $E$ be a ring homomorphism from the centralizer subring of the set consisting of all $\Phi.\mathrm{actEnd}\ a$ together with $\Phi.\mathrm{varpiEnd}$ into $M_2(\mathbb Q_p)$, and assume: (hNe) each $e$ in that centralizer induces at least one additive endomorphism $N_e$ of $D.\mathrm{NMod}$ with $N_e(\mathrm{nMk}(x_1,x_2)) = \mathrm{nMk}(e_*x_1, e_*x_2)$ for all $x$, the action on the twisted factor taken through $\mathrm{ofSigma}$ and $\mathrm{toSigma}$; and (hE) for each such $e$ there is a matrix $A$ over $\mathbb Z_p$ with $p\,E(e)$ the image of $A$ in $M_2(\mathbb Q_p)$, such that every $N_e$ satisfying the above compatibility satisfies $p\,N_e(r_\Phi w) = r_\Phi(Aw)$ for all $w \in \mathbb Z_p^2$. Then $E$ is injective.
--
--   This is the faithfulness half of the comparison, in the Čerednik–Drinfeld theory of special formal $\mathcal O_D$-modules of height $4$, between the endomorphism ring of $\Phi$ commuting with the $W(\mathbb F_{p^2})$-action and with $\varpi$ and the matrix algebra $M_2(\mathbb Q_p)$, the representation being pinned down by its compatibility with the rigidification $r_\Phi$ of the degree-$0$ part of $\eta$. It feeds the combined statement [`CerednikDrinfeld.FormalODModule.injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat`](thm.html#CerednikDrinfeld.FormalODModule.injective_and_exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_injective_of_ringHom_centralizer_rigidification_compat.lean

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

theorem CerednikDrinfeld.FormalODModule.injective_of_ringHom_centralizer_rigidification_compat
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
    Function.Injective E := by sorry
