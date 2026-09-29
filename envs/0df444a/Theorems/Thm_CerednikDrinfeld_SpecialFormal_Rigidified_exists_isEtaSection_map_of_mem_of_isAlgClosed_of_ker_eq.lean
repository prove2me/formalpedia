-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/d5b865ce-2a6f-5901-bc01-295f3802ac23
-- title:
--   Transfer of η-sections along a geometric point
-- statement:
--   Fix a prime $p$, a commutative ring $O$, a ring homomorphism $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and a formal $O_D$-module $\Phi$ over $O/pO$; write $\bar\jmath = \iota$ followed by reduction mod $p$. Assume: $\Phi$ is special for $\bar\jmath$ (its Lie algebra splits as the direct sum of the weight pieces `lieZero` and `lieOne`, both invertible modules), $\Phi$ has height $4$, `lieZero` is contained in the kernel of the $\varpi$-action on the Lie algebra, the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary (witness $h_{c\Phi}$), and there is an additive map $r_\Phi : \mathbb{Z}_p^2 \to N(\Phi)$ into the $N$-module of the associated graded Cartier module data such that a canonical $L$-map exists and, for every canonical $L$-map $L$, $r_\Phi$ is a bijection from all of $\mathbb{Z}_p^2$ onto the degree-$0$ $\eta$-piece of $L$. Let $B$ be a Noetherian commutative $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : O \to B$ a ring map, $t$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$, and $i \in \{0,1\}$. Let $N$ assign to each prime $x$ of $B$ the $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$ consisting of those $v$ for which there are $f \notin x$, gradedness witnesses over the localisation $B_f$ for $t$, for its reduction and for $\Phi$, a canonical $L$-map, and an element $z$ making `IsEtaSection` hold in degree $i$ for $v$. Finally let $L$ be an algebraically closed field that is a $\mathbb{Z}_p$-algebra, $g : B \to L$ a ring map compatible with the structure maps from $\mathbb{Z}_p$, $x$ a prime of $B$ with $\ker g = x$, and assume the base change $t \otimes_g L$ is admissible for $(\iota, g \circ \psi)$. The conclusion is that for every point $x'$ of $\operatorname{Spec} L$ and every $v \in \mathbb{Q}_p^2$ with $v \in N(x)$ there exist $f \notin x'$, gradedness witnesses over $L_f$ for $t \otimes_g L$, for its reduction and for $\Phi$, a canonical $L$-map $L'$, and an element $z$ such that `IsEtaSection` holds for $t \otimes_g L$ in degree $i$ at $v$ with these data.
--
--   This is the functoriality, or specialisation, step in the Čerednik–Drinfeld comparison: a germ of the $i$-th $\eta$-section at a point $x$ of $\operatorname{Spec} B$ restricts to a section of the same kind over the geometric fibre at $x$. It is used by the two degree-specific characterisations `mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq` and `mem_iff_exists_isEtaSection_one_map_of_isAlgClosed_of_ker_eq`, which identify the lattice $N(x)$ with the lattice read off from the geometric fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
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
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (i : Fin 2) (N : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v)

    {L : Type} [Field L] [IsAlgClosed L] [Algebra ℤ_[p] L] (g : B →+* L)
    (hg : g.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] L)
    (x : PrimeSpectrum B) (hx : RingHom.ker g = x.asIdeal)
    (ht' : (t.map g).IsAdmissible ι (g.comp ψ)) :
    ∀ (x' : PrimeSpectrum L) (v : Fin 2 → ℚ_[p]), v ∈ N x →
      ∃ (f : L) (_ : f ∉ x'.asIdeal) (hc : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom f))
        (hcb : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom f))
        (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom f))
        (L' : _) (hL' : (((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L'),
        ∃ z, (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L' hL' i z v := by sorry
