-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_of_mem_etaPiece_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_of_mem_etaPiece_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/b31ee643-6bc0-5654-9a4a-f3e8ec04e49a
-- title:
--   Rigidified coordinates exist for elements of ηᵢ(L')
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota : W(\mathbb F_{p^2}) \to W(k)$; write $\bar j$ for $\iota$ followed by the quotient map $W(k) \to W(k)/pW(k)$. Let $\Phi$ be a formal $O_D$-module over $W(k)/pW(k)$, i.e. a commutative $2$-dimensional formal group law with a $W(\mathbb F_{p^2})$-action and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$. It is assumed that $\Phi$ is special for $\bar j$ (its Lie algebra is the direct sum of the invertible eigen-submodules `lieZero` and `lieOne`), that $\Phi$ has height $4$ (the kernel of $[p]$ is finite projective of rank $p^4$ over every field-valued point), that `lieZero` is annihilated by the linear part `lieVarpi` of $\varpi$, and that the graded pieces of degree $0$ and $1$ of the Cartier module of $\Phi$ — the $f$ on which the Teichmüller element $c$ acts by the homothety $\bar j(\tau(c))^{p^n}$ — are complementary, this complement being `hcΦ`. Let $r_\Phi : \mathbb Z_p^2 \to N(\Phi)$ be an additive map into the $N$-module of the graded Cartier module data attached to $\Phi$ and `hcΦ`, and assume that for every canonical $L$-map $L$ of that data, $r_\Phi$ maps $\mathbb Z_p^2$ bijectively onto `etaPiece` $L$ in degree $0$, i.e. onto $\eta(L)$ intersected with the degree-$0$ piece. Let $K$ be an algebraically closed field of characteristic $p$ which is a $\mathbb Z_p$-algebra, with $p$ nilpotent in $K$, and $\psi' : W(k)\to K$ a ring homomorphism. Let $t'$ be a rigidified object over $K$, consisting of a formal $O_D$-module $t'.X$ over $K$, an integer $t'.n$ and a series $t'.\rho$ over $K/pK$, and assume $t'$ admissible for $(\iota,\psi')$: $t'.X$ is special for $\psi'\circ\iota$, has height $4$, and $t'.\rho$ is an isogeny of height $4\,t'.n$ from $\Phi$ base changed along $\psi'$ to the reduction of $t'.X$. Work over the localisation of $K$ away from $1$, with base-change map `Rigidified.awayHom (1 : K)`, and assume the degree-$0$ and degree-$1$ graded pieces are complementary for `t'.XS` (hypothesis `hc`), for `t'.XbarS` (hypothesis `hcb`) and for the base change of $\Phi$ (hypothesis `hcΦ1`). Let $L'$ be an additive map from the Cartier module of `t'.XS` to its $N$-module which is a canonical $L$-map (a Cartier $L$-map, $\sigma$-semilinear, sending $V x$ to the class of $(\varpi x,0)$ and lifting Frobenius through $\lambda$, and induced by base change from a Cartier $L$-map on a special graded Cartier module data over a $p$-torsion-free surjecting base). Finally let $i \in \{0,1\}$ and let $z$ lie in `etaPiece` $L'$ in degree $i$, i.e. in $\eta(L')$ intersected with the degree-$i$ piece. The conclusion is that there exists $v \in \mathbb Q_p^2$ such that `t'.IsEtaSection` holds for $z$ and $v$: namely $z$ lies in that same `etaPiece`, and the lattice relation holds for $p^i v$ and for the image of $\varpi_N^{\,i} z$ under the reduction map `etaRed` to the $N$-module of `t'.XbarS`, that is, there are $m, k \in \mathbb N$ and $w \in \mathbb Z_p^2$ with $p^m\,(p^i v) = w$ in $\mathbb Q_p^2$ and $p^k\,\mathrm{rigidNum}(w) = p^{k + t'.n + m}\,\overline{z}$, where $\mathrm{rigidNum}$ is the composite of $r_\Phi$ with the base change and the map induced by $t'.\rho$, the latter supplied by the `IsODHom` component of the isogeny condition in admissibility.
--
--   This is the existence half of the identification of the $\eta$-pieces, after tensoring with $\mathbb Q$, with $\mathbb Q_p^2$: every element of $\eta_i(L')$ admits rigidified coordinates relative to the numbering $r_\Phi$ fixed on the $\eta$-piece of $\Phi$. It feeds the surjectivity of the stalk map in `stalkMap_surjective_of_tangent_germ_wittVector`, part of the Čerednik–Drinfeld description of the formal upper half plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_of_mem_etaPiece_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_of_mem_etaPiece_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ' : WittVector p k →+* K) (hK : IsNilpotent (p : K))
    (t' : Rigidified p Φ K) (ht' : t'.IsAdmissible ι ψ')
    (hc : t'.IsGradedS ι ψ' (Rigidified.awayHom (1 : K))) (hcb : t'.IsGradedSbar ι ψ' (Rigidified.awayHom (1 : K)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' (Rigidified.awayHom (1 : K)))
    (L' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).M →+
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod)
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L')
    (i : Fin 2)
    (z : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) (hz : z ∈ ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).etaPiece L' hL'.isCartierLMap.map_verschiebung i) :
    ∃ v : Fin 2 → ℚ_[p], t'.IsEtaSection ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hc hcb hcΦ1 L' hL' i z v := by sorry
