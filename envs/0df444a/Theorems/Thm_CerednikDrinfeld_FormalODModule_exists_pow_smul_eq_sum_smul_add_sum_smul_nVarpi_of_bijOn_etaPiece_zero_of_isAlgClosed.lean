-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/a927ad76-2343-5b82-8a5f-ea615fe6cc18
-- title:
--   N-span of η_{Φ,0} and Piη_{Φ,0} up to pᵃ
-- statement:
--   Fix a prime $p$, a field $k$ of characteristic $p$ that is algebraically closed, and a ring homomorphism $\iota$ from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ to $W(k)$; write $B = W(k)/pW(k)$ and let $j$ be $\iota$ followed by the quotient map, so $j : \mathbb{Z}_{p^2} \to B$. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $B$, i.e. a two-dimensional commutative formal group law $\Phi.F$ with an action of $\mathbb{Z}_{p^2}$ by endomorphisms and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma(a)]\circ\varpi$. Assume: $\Phi$ is special for $j$ (its zero and one Lie pieces are complementary and both invertible $B$-modules); $\Phi$ has height $4$, meaning $[p]$ has kernel of degree $p^4$; and the two graded pieces of the Cartier module $M =$ `CartierModule p Φ.F` for $j$ in degrees $0$ and $1$ are complementary additive subgroups, where the degree-$n$ piece consists of those $f$ with $[\,\omega\,]\cdot f = j(\omega)^{p^n} f$ for all Teichmüller lifts $\omega$ of elements of $\mathbb{F}_{p^2}$. Let $D$ be the resulting graded Cartier module datum (with $M$, Frobenius, Verschiebung, $\varpi$ and the two pieces) and $N = D.\mathrm{NMod}$ the quotient of $M \times \Sigma$ by the relation `nRel`. Let $r_\Phi : \mathbb{Z}_p^2 \to N$ be additive and assume that for every canonical $L$-map $L : M \to N$ (an additive map satisfying the predicate `IsCanonicalLMap`), $r_\Phi$ maps all of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$, the intersection of $\eta(L)$ with the $0$-th piece of $N$. Then there is $a \in \mathbb{N}$ such that every $x \in N$ satisfies $p^a x = \sum_{i\in\{0,1\}} c_i\, r_\Phi(e_i) + \sum_{i\in\{0,1\}} d_i\, \Pi\, r_\Phi(e_i)$ for suitable $c_i, d_i \in W(B)$, where $e_0,e_1$ are the standard basis vectors of $\mathbb{Z}_p^2$ and $\Pi$ is the map `nVarpi` induced on $N$ by $\varpi$ on both coordinates.
--
--   This is the spanning statement for the Boutot–Carayol module $N(M_\Phi)$ attached to a special formal $\mathcal{O}_D$-module of height $4$ over $W(k)/p$: the image of the rigidifying map $r_\Phi$ together with its $\Pi$-translates generates $N$ over $W(W(k)/p)$ after multiplication by a fixed power of $p$. It is used in the rigidity part of the Čerednik–Drinfeld uniformisation, feeding the injectivity statement for the centralizer action on rigidifications and the corresponding spanning result for rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed.lean

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
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _)) :
    ∃ a : ℕ, ∀ x : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      ∃ c d : Fin 2 → WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k)),
        p ^ a • x = (∑ i : Fin 2, c i • rΦ (Pi.single i 1)) +
          ∑ i : Fin 2, d i • (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nVarpi (rΦ (Pi.single i 1)) := by sorry
