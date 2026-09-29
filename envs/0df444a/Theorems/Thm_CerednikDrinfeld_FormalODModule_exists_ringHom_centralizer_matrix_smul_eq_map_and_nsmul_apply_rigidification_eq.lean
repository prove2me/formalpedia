-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq
-- name    : CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/a5e37e6c-f801-5700-aa51-91f5c276bf14
-- title:
--   Endomorphisms of a special formal module as p-adic matrices
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : W(\mathbb F_{p^2}) \to W(k)$ a ring homomorphism; write $j$ for $\iota$ followed by reduction modulo the ideal $pW(k)$. Let $\Phi$ be a formal $\mathcal O_D$-module over $W(k)/pW(k)$, that is, a commutative two-dimensional formal group law $\Phi.F$ together with an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$, subject to: $\Phi$ is special for $j$ (the Lie algebra is the direct sum of the eigenspaces $\mathrm{lieZero}\,j$ and $\mathrm{lieOne}\,j$, both invertible modules); $\Phi$ has height $4$, i.e. the kernel of multiplication by $p$ is finite projective with fibre dimension $p^4$; and the graded pieces of the Cartier module $M = \mathrm{CartierModule}\,p\,\Phi.F$ in degrees $0$ and $1$, defined by $\Phi(\tau(c))_* f = [\,j(\tau(c))^{p^n}\,]f$ for all $c \in \mathbb F_{p^2}$, are complementary (hypothesis $h_{c\Phi}$). Let $D$ be the resulting graded Cartier module datum, with underlying module $M$, Frobenius, Verschiebung, $\varpi$ and the two graded submodules, and let $N = D.\mathrm{NMod}$ be the quotient of $M \times \Sigma$ (where $\Sigma$ is $M$ with Witt-scalars twisted by Frobenius) by the submodule $D.\mathrm{nRel}$, with quotient map $\mathrm{nMk}$. Let $r_\Phi : \mathbb Z_p^2 \to N$ be an additive map which, for every additive $L : M \to N$ that is a canonical $L$-map for $D$, maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ eta piece $D.\mathrm{etaPiece}\,L\,\cdot\,0$. Then there is a ring homomorphism $E$ from the centralizer, inside $\mathrm{End}(\Phi.F)$, of the set consisting of all $\Phi.\mathrm{actEnd}\,a$ together with $\Phi.\mathrm{varpiEnd}$, to $M_2(\mathbb Q_p)$, such that: first, every element $e$ of that centralizer admits an additive endomorphism $N_e$ of $N$ with $N_e(\mathrm{nMk}(x_1,x_2)) = \mathrm{nMk}(e_*x_1, e_*x_2)$ for all $(x_1,x_2) \in M \times \Sigma$, the action on the second coordinate being $e_*$ transported through the identifications $\mathrm{ofSigma}$, $\mathrm{toSigma}$; and second, for every such $e$ there is a matrix $A \in M_2(\mathbb Z_p)$ with $p\,E(e)$ equal to the image of $A$ in $M_2(\mathbb Q_p)$, and such that every additive endomorphism $N_e$ of $N$ satisfying the above compatibility obeys $p\,N_e(r_\Phi(w)) = r_\Phi(Aw)$ for all $w \in \mathbb Z_p^2$.
--
--   This is the step in the Čerednik–Drinfeld theory which makes the commutant of the $\mathcal O_D$-action on a special formal module of height $4$ act on the rank-two $\mathbb Z_p$-lattice cut out by the rigidification $r_\Phi$, the action being integral only after multiplication by $p$, since the canonical $L$-map is functorial up to one factor of $p$. It is used in the construction of isogenies of formal $\mathcal O_D$-modules matching prescribed rigidification data and in the refinement asserting injectivity of $E$ together with compatibility with rigidifications.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _)) :
    ∃ E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p],
      (∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2))))) ∧
      (∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p],
        (p : ℚ_[p]) • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) ∧
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p • Ne (rΦ w) = rΦ (A.mulVec w)) := by sorry
