-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_injective_and_rigidification_compat
-- name    : CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_matrix_injective_and_rigidification_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/1ee1b611-11cf-5a39-9274-425569163cf9
-- title:
--   An order in M₂(ℚₚ) acting compatibly with a rigidification
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$, let $\iota : \mathrm{Zp2}\,p = W(\mathbb{F}_{p^2}) \to W(k)$ be a ring homomorphism, write $j$ for $\iota$ followed by the reduction $W(k) \to W(k)/pW(k)$, and let $\Phi$ be a formal $\mathcal{O}_D$-module over $W(k)/pW(k)$ (a commutative two-dimensional formal group law $\Phi.F$ with an action of $W(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ satisfying $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$). Assume: $\Phi$ is special for $j$, that is, the two eigen-submodules `lieZero` and `lieOne` of the Lie algebra are complementary and invertible; $\Phi$ has height $4$, that is, the kernel of the action of $p$ is finite projective of rank $p^4$ over every field-valued base; the graded pieces of the Cartier module of $\Phi$ in degrees $0$ and $1$ for $j$ are complementary, giving graded Cartier module data $D = \Phi.\mathrm{toGradedCartierModuleData}\,j$; and $r_\Phi : \mathbb{Z}_p^2 \to D.\mathrm{NMod}$ is an additive map which, for every canonical $L$-map $L$ on $D$, maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ piece $D.\mathrm{etaPiece}\,L\,\cdot\,0$. The conclusion asserts the existence of a ring homomorphism $E$ from the centralizer subring of $\{\,[a] : a \in W(\mathbb{F}_{p^2})\,\} \cup \{\varpi\}$ inside $\operatorname{End}(\Phi.F)$ to $M_2(\mathbb{Q}_p)$, together with an exponent $m \in \mathbb{N}$, such that: $E$ is injective; every $A \in M_2(\mathbb{Z}_p)$ is hit in the form $E(e) = p^m A$, so $p^m M_2(\mathbb{Z}_p) \subseteq \operatorname{im} E$; $p^m E(e) \in M_2(\mathbb{Z}_p)$ for every $e$; and the representation is compatible with the rigidification, in the sense that whenever $p^m E(e) = A$ with $A$ integral and $N_e$ is an additive endomorphism of $D.\mathrm{NMod}$ induced by $e$ on representatives (that is, $N_e(D.\mathrm{nMk}\,x)$ equals $D.\mathrm{nMk}$ of the pair obtained by applying the Cartier-module action `endAct` of $e$ to both coordinates of $x$, the second through the identifications `ofSigma` and `toSigma`), then $p^m N_e(r_\Phi w) = r_\Phi(Aw)$ for all $w \in \mathbb{Z}_p^2$.
--
--   This is the local input, at a base point of the moduli problem, for the identification of the $\mathcal{O}_D$-linear endomorphism ring of a special formal module of height $4$ over $W(k)/p$ with an order of $M_2(\mathbb{Q}_p)$, written so that the matrix action is the one induced on the rigidifying lattice $r_\Phi(\mathbb{Z}_p^2)$ inside the $N$-module of the graded Cartier data. It is used in the construction of Drinfeld data from rigidified special formal modules, where it supplies the $\mathrm{GL}_2$-equivariance of the period morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_injective_and_rigidification_compat.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_matrix_injective_and_rigidification_compat
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _)) :
    ∃ (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]) (m : ℕ),
      Function.Injective E ∧
      (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ e, E e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
      (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
      (∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) →
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p ^ m • Ne (rΦ w) = rΦ (A.mulVec w)) := by sorry
