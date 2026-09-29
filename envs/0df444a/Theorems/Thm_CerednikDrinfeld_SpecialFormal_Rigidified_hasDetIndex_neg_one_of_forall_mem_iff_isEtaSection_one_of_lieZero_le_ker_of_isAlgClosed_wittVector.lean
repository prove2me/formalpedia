-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_hasDetIndex_neg_one_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_of_isAlgClosed_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_neg_one_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_of_isAlgClosed_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/2f734566-35bf-55d7-8bd4-db677b7ede30
-- title:
--   Determinant index -1 of the odd η-lattice over an algebraically closed base
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : W(\mathbb F_{p^2}) \to W(k)$ a ring homomorphism; write $\bar\jmath$ for $\iota$ followed by reduction modulo $p$. Let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/p$ subject to: $\Phi$ is special for $\bar\jmath$ (its Lie algebra is the direct sum of the $\bar\jmath$-eigenspace $\mathrm{lieZero}$ and the $\bar\jmath\circ\sigma$-eigenspace $\mathrm{lieOne}$, both invertible modules), $\Phi$ has height $4$, $\mathrm{lieZero}$ lies in the kernel of the linear part of $\varpi$, and the degree-$0$ and degree-$1$ Teichmüller eigen-pieces of the Cartier module of $\Phi$ are complementary (hypothesis $h_{c\Phi}$, giving graded Cartier module data for $\Phi$); further, an additive map $r_\Phi : \mathbb Z_p^2 \to N(\Phi)$ is given, a canonical $L$-map for these data exists, and for every canonical $L$ the map $r_\Phi$ is a bijection of $\mathbb Z_p^2$ onto the degree-$0$ $\eta$-piece attached to $L$. Let $B$ be an algebraically closed field that is a $\mathbb Z_p$-algebra with $p$ nilpotent, $\psi : W(k) \to B$ a ring homomorphism, and $t = (X,n,\rho)$ a rigidified object over $B$ that is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$. Finally let $x \mapsto N_1(x)$ assign to each prime of $B$ a $\mathbb Z_p$-submodule of $\mathbb Q_p^2$, with membership $v \in N_1(x)$ equivalent to the existence of some $f \notin x$, of the three complementarity data for $X$, $\bar X$ and the base-changed $\Phi$ over $B_f$, of a canonical $L$-map there, and of an element $z$ for which $\mathrm{IsEtaSection}$ holds in degree $1$ for $z$ and $v$. The conclusion is that for every prime $x$ of $B$ with $\varpi(\mathrm{lieOne}(X)) \subseteq x\cdot \mathrm{lieZero}(X)$, the lattice $N_1(x)$ has determinant index $-1$ with respect to $p$: there is $g \in \mathrm{GL}_2(\mathbb Q_p)$ with $g\,\mathbb Z_p^2 = N_1(x)$ and $\det g = u p^{-1}$ for some unit $u \in \mathbb Z_p^\times$.
--
--   This is the odd half of Drinfeld's condition (C3) for the functor attached to special formal $O_D$-modules: on the stratum where $1$ is critical for $X$ and $0$ is critical for $\Phi$, the $\eta$-lattice in degree $1$ is a lattice of determinant index $-1$, as in Boutot–Carayol. It feeds the corresponding statement formulated without the hypothesis that the base field is algebraically closed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_hasDetIndex_neg_one_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_of_isAlgClosed_wittVector.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_neg_one_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_of_isAlgClosed_wittVector
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [Field B] [IsAlgClosed B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v) :
    ∀ x : PrimeSpectrum B,
      Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieZero (structureMap ι ψ) →
      FormalOmega.HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) (N₁ x) (-1) := by sorry
