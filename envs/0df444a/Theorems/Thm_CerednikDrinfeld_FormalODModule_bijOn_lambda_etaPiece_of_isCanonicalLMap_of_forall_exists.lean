-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists
-- name    : CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/b2fed6bc-c120-590d-a7ff-01c31af203fa
-- title:
--   λ maps ηₙ bijectively onto the varpi=V locus
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$, let $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to W(k)$ be a ring homomorphism, and let $\Phi$ be a formal $\mathcal{O}_D$-module over $W(k)/pW(k)$, i.e. a two-dimensional commutative formal group law with an action of $\mathbb{W}(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ satisfying $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$. Write $j$ for $\iota$ followed by reduction modulo $pW(k)$. Assume $\Phi$ is special for $j$ (its Lie algebra is the direct sum of the $j$- and $j\circ\sigma$-eigenspaces of the action, each an invertible module), that $\Phi$ has height $4$ (the kernel of $[p]$ has degree $p^4$), and that the two graded pieces of the Cartier module $M =$ `CartierModule p Φ.F` for $j$ in degrees $0$ and $1$ — the eigenspaces where the Teichmüller action of $c \in \mathbb{F}_{p^2}$ acts by the homothety $j(\tau c)^{p^n}$ — are complementary; let $D$ be the resulting graded Cartier module datum, with $\varpi$, the Frobenius and the integral Verschiebung $V$ on $M$. Let $L : M \to N(M)$ be an additive map which is a canonical $L$-map for $D$, and $n \in \mathbb{Z}/2$. Assume further that every $z$ in the piece of degree $n+1$ can be written $z = \varpi m + V m'$ with $m$ in the piece of degree $n$ and $m' \in M$, and that for $m$ in the piece of degree $n$, $\varpi m \in V M$ implies $m \in V M$. Then $\lambda_M : N(M) \to M$, induced by $(m,m') \mapsto \varpi m + V m'$, restricts to a bijection from the subgroup `etaPiece L _ n` (the intersection of the subgroup `eta` attached to $L$ with the image in $N(M)$ of the product of the degree-$n$ piece with itself) onto the set of $m$ lying in the piece of degree $n+1$ with $\varpi m = V m$.
--
--   This is the identification of the $n$-th graded part of $\eta(L)$ with the locus $\varpi m = V m$ in the next graded piece, at an index where $\varpi$ induces a bijection $M_n/VM \to M_{n+1}/VM$, in Boutot and Carayol's Cartier-theoretic study of special formal $\mathcal{O}_D$-modules of height $4$ over an algebraically closed residue field. It feeds the construction of an additive map that is bijective on the degree-zero part of $\eta(L)$, and thence the freeness of rank two used in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists.lean

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

theorem CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod) (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L)
    (n : Fin 2)
    (hsurj : ∀ z ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((n + 1 : Fin 2) : ℕ), ∃ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (n : ℕ),
      ∃ m' : MvFormalGroup.CartierModule p Φ.F, z = MvFormalGroup.CartierModule.endAct Φ.varpiEnd m + MvFormalGroup.CartierModule.verschiebungInt m')
    (hinj : ∀ m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) (n : ℕ),
      (∃ g : MvFormalGroup.CartierModule p Φ.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct Φ.varpiEnd m) →
        ∃ g' : MvFormalGroup.CartierModule p Φ.F, MvFormalGroup.CartierModule.verschiebungInt g' = m) :
    Set.BijOn (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).lambda
      ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung n : Set _)
      {m : MvFormalGroup.CartierModule p Φ.F | m ∈ Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ((n + 1 : Fin 2) : ℕ) ∧ MvFormalGroup.CartierModule.endAct Φ.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m} := by sorry
