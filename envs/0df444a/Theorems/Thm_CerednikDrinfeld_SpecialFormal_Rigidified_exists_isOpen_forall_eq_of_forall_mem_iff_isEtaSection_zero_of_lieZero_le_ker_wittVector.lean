-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/d0307e5b-5e45-51f2-b988-cc9feb0cdced
-- title:
--   Local constancy of N₀ on the index-zero locus
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $O_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$, with the induced character $\bar\jmath = \iota$ followed by reduction. Assume: $\Phi$ is special for $\bar\jmath$, meaning that the eigen-submodules $\mathrm{Lie}_0$ and $\mathrm{Lie}_1$ of its Lie algebra are complementary and each invertible; $\Phi$ has height $4$; the linear part of $\varpi$ kills $\mathrm{Lie}_0$; the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary, giving the graded Cartier datum $D_\Phi$; an additive map $r_\Phi : \mathbb{Z}_p^2 \to N(D_\Phi)$ is given; a canonical $L$-map for $D_\Phi$ exists; and for every canonical $L$-map $L$ the map $r_\Phi$ sends all of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece attached to $L$. Let $B$ be a noetherian commutative $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : W(k) \to B$ a ring homomorphism, and $t$ a rigidified datum over $B$ (a formal $O_D$-module $X$, an integer $n$, and a series $\rho$ over $B/p$) which is admissible for $(\iota,\psi)$: $X$ is special for the structure character, has height $4$, and $\rho$ is an isogeny of height $4n$ from the base change of $\Phi$ to the reduction of $X$. Let $N_0$ assign to each prime $x$ of $B$ a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$, and assume the pointwise description $hN_0$: a vector $v$ lies in $N_0(x)$ exactly when there is $f \notin x$ such that, over the localisation $B_f$, the three complementarity conditions `IsGradedS`, `IsGradedSbar` and `IsGradedPhiS` hold, and for some canonical $L$-map $L$ there is an element $z$ with `IsEtaSection` in degree $0$ relating $z$ and $v$. The conclusion: for every prime $x$ of $B$ such that the image of $\mathrm{Lie}_0(X)$ under the linear part of $\varpi$ lies in $x \cdot \mathrm{Lie}_1(X)$, there is an open neighbourhood $U$ of $x$ in $\operatorname{Spec} B$ such that $N_0(y) = N_0(x)$ for every $y \in U$ satisfying the same inclusion.
--
--   This is the local constancy of the $\eta$-lattice $N_0$ along the locus of primes where the index $0$ is critical, in the Čerednik–Drinfeld uniformisation of special formal $O_D$-modules. It feeds the construction of the lattice-valued datum attached to a rigidified special formal module, being cited in the proof that $N_0$ is a full lattice described by $\eta$-sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
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
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₀ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) :
    ∀ x : PrimeSpectrum B,
      Submodule.map t.X.lieVarpi (t.X.lieZero (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieOne (structureMap ι ψ) →
      ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, Submodule.map t.X.lieVarpi (t.X.lieZero (structureMap ι ψ)) ≤ y.asIdeal • t.X.lieOne (structureMap ι ψ) →
          N₀ y = N₀ x := by sorry
