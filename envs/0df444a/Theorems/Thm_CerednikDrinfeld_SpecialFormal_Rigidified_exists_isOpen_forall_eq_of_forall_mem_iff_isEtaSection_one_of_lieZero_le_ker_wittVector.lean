-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a38faf87-1505-55cf-96ae-613f12ef6b14
-- title:
--   Local constancy of N₁ on the 1-critical locus
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota \colon W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$ (a commutative formal group law in two variables with an action of $W(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$). Assume: $\Phi$ is special for $\bar\jmath = \iota \bmod p$, i.e. its Lie algebra is the direct sum of the weight-$\bar\jmath$ part $\mathrm{lieZero}$ and the weight-$\bar\jmath\circ\sigma$ part $\mathrm{lieOne}$, both invertible modules; the kernel of $[p]$ on $\Phi$ has degree $p^4$; $\mathrm{lieZero}$ is killed by the linear part of $\varpi$; the graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary (hypothesis $h_{c\Phi}$), so that a graded Cartier module datum $D_\Phi$ is obtained; an additive map $r_\Phi \colon \mathbb{Z}_p^2 \to D_\Phi.\mathrm{NMod}$ is given; a canonical $L$-map on $D_\Phi$ exists; and for every canonical $L$-map $L$, $r_\Phi$ maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\mathrm{etaPiece}\,L\,\_\,0$. Let $B$ be a noetherian commutative $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi \colon W(k) \to B$ a ring homomorphism, and $t = (X, n, \rho)$ a rigidification over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, its $[p]$-kernel has degree $p^4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$. Let $N_1$ assign to each point $x$ of $\operatorname{Spec} B$ a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$, subject to the characterisation $h_{N_1}$: $v \in N_1(x)$ if and only if there are $f \notin x$, complementarity data for the degree-$0$ and degree-$1$ graded pieces of the Cartier modules of $X$, of its reduction and of the reduction of $\Phi$ over the localisation $B_f$, a canonical $L$-map $L$ there, and an element $z$ with $\mathrm{IsEtaSection}$ at index $1$ for $v$, that is: $z$ lies in the degree-$1$ $\eta$-piece determined by $L$, and the reduction of $\mathrm{nVarpi}(z)$ satisfies the lattice relation of level $n$ with respect to the rigidified numbering built from $r_\Phi$ and $p\cdot v$. Then for every $x \in \operatorname{Spec} B$ such that the image of $\mathrm{lieOne}(X)$ under the linear part of $\varpi$ is contained in $x \cdot \mathrm{lieZero}(X)$, there is an open $U \ni x$ such that every $y \in U$ satisfying the same containment has $N_1(y) = N_1(x)$.
--
--   The submodules $N_1(x)$ are the $p$-adic lattices read off from the $\eta$-sections of the Cartier module of a rigidified special formal $\mathcal{O}_D$-module, in the Čerednik–Drinfeld uniformisation of Shimura curves as carried out by Boutot and Carayol; the locus where $\varpi$ kills $\mathrm{lieOne}$ modulo the point is the stratum on which the index $1$ is critical. This local constancy statement is used in the construction of the Deligne datum attached to a rigidification, where $N_1$ must be shown to be a full lattice varying locally constantly on that stratum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isOpen_forall_eq_of_forall_mem_iff_isEtaSection_one_of_lieZero_le_ker_wittVector
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
    (N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v) :
    ∀ x : PrimeSpectrum B,
      Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieZero (structureMap ι ψ) →
      ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ y.asIdeal • t.X.lieZero (structureMap ι ψ) →
          N₁ y = N₁ x := by sorry
