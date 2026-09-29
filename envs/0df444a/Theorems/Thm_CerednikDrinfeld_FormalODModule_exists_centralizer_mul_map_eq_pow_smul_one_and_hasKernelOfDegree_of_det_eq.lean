-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq
-- name    : CerednikDrinfeld.FormalODModule.exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/1a1197e0-dee9-5025-8cf0-2ebfaf3d0171
-- title:
--   Inverting an integral matrix by an 𝒪_D-linear endomorphism
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$, with $j$ the composite of $\iota$ with the quotient map. Assume: $\Phi$ is special for $j$, i.e. the Lie algebra splits as the direct sum of the eigenspaces $\mathrm{lieZero}$ and $\mathrm{lieOne}$, both invertible modules; $\Phi$ has height $4$, i.e. multiplication by $p$ has kernel algebra finite projective of rank $p^4$ over every field-valued point; the graded pieces in degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary, giving graded Cartier module data $D$; $r_\Phi : \mathbb{Z}_p^2 \to D.\mathrm{NMod}$ is an additive map which, for every canonical $L$-map $L$, maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$; $E$ is a ring homomorphism from the centralizer of $\{\Phi.\mathrm{actEnd}\,a\} \cup \{\Phi.\mathrm{varpiEnd}\}$ in $\mathrm{End}(\Phi.F)$ to $M_2(\mathbb{Q}_p)$; every $e$ in that centralizer induces an additive endomorphism $N_e$ of $D.\mathrm{NMod}$ compatible with the action of $e$ on Cartier module and $\Sigma$ components through $\mathrm{nMk}$; and for every $e$ there is an integral matrix $A_e$ with $p\,E(e) = A_e$ and $p\,N_e(r_\Phi w) = r_\Phi(A_e w)$ for all such $N_e$ and all $w \in \mathbb{Z}_p^2$. Then for every $A \in M_2(\mathbb{Z}_p)$ with $\det A = u p^v$, $u \in \mathbb{Z}_p^\times$ and $v \in \mathbb{N}$, there are $e$ in the centralizer and $c \in \mathbb{N}$ with $E(e)\,A = p^{c+v} \cdot 1$ in $M_2(\mathbb{Q}_p)$, such that the power series of $e$ has kernel algebra finite projective over $W(k)/p$ of rank $p^{4c+2v}$ at every field-valued point, and is an $\mathcal{O}_D$-homomorphism $\Phi \to \Phi$, i.e. a homomorphism of formal group laws commuting with all $\Phi.\mathrm{act}\,a$ and with $\Phi.\mathrm{varpi}$.
--
--   This is the surjectivity-up-to-$p$-powers (cofullness) step for the quasi-isogeny algebra of a special formal $\mathcal{O}_D$-module of height $4$ over an algebraically closed residue field, in the form used in the Čerednik–Drinfel'd uniformisation: an arbitrary integral matrix is inverted, up to a power of $p$, by an $\mathcal{O}_D$-linear endomorphism whose kernel degree is computed from the valuation of the determinant. It feeds the construction of isogenies of prescribed height attached to nodes in `exists_isIsogenyOfHeight_map_node_rigidNum_single_eq`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_centralizer_mul_map_eq_pow_smul_one_and_hasKernelOfDegree_of_det_eq
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
          ∀ w : Fin 2 → ℤ_[p], p • Ne (rΦ w) = rΦ (A.mulVec w))
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) (v : ℕ) (u : ℤ_[p]ˣ) (hA : A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ v) :
    ∃ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (c : ℕ),
      E e * A.map ((↑) : ℤ_[p] → ℚ_[p]) = ((p : ℚ_[p]) ^ (c + v)) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∧
      FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (4 * c + 2 * v)) ∧
      FormalODModule.IsODHom Φ Φ (e : MvFormalGroup.End Φ.F).toPowerSeries := by sorry
