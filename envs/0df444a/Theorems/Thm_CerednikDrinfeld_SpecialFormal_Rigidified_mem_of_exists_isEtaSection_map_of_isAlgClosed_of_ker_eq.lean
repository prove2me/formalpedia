-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/92e6a441-f417-57ec-8d99-0b6a3587b7ec
-- title:
--   Eta-sections over the geometric fibre lie in the germ lattice
-- statement:
--   Fix a prime $p$, a commutative ring $O$, a ring map $\iota : \mathbb{Z}_{p^2} \to O$ and a formal $O_D$-module $\Phi$ over $O/pO$, and assume: $\Phi$ is special for $\bar\jmath = \iota$ followed by reduction mod $p$ (its zero and one Lie pieces are complementary and invertible), $\Phi$ has height $4$, the zero Lie piece lies in $\ker(\mathrm{Lie}\,\varpi)$, the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary (hypothesis `hcΦ`), and $r_\Phi : \mathbb{Z}_p^2 \to N(\Phi)$ is an additive map for the associated graded Cartier module data such that a canonical $L$-map exists and, for every canonical $L$-map $L$, $r_\Phi$ maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\eta(L)\cap N_0$. Let $B$ be a Noetherian $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : O \to B$ a ring map, $t = (X, n, \rho)$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$, $i \in \{0,1\}$, and $N$ an assignment of a $\mathbb{Z}_p$-submodule $N(x) \subseteq \mathbb{Q}_p^2$ to each $x \in \operatorname{Spec} B$ such that $v \in N(x)$ holds exactly when, for some $f \notin \mathfrak p_x$, the localisation $B_f$ carries the required gradings (for $X_f$, for $\bar X_f$ and for $\bar\Phi_f$), a canonical $L$-map $L$, and an element $z$ with $\mathrm{IsEtaSection}$ in degree $i$ relating $z$ to $v$. Let finally $L$ be an algebraically closed $\mathbb{Z}_p$-algebra field, $g : B \to L$ a ring map compatible with the $\mathbb{Z}_p$-structures, $x \in \operatorname{Spec} B$ with $\ker g = \mathfrak p_x$, and assume the base change $t \otimes_g L$ is admissible for $(\iota, g\circ\psi)$. Then for every $x' \in \operatorname{Spec} L$ and every $v \in \mathbb{Q}_p^2$: if over some $f \notin \mathfrak p_{x'}$ there are gradings, a canonical $L$-map $L'$ and an element $z$ with $(t \otimes_g L).\mathrm{IsEtaSection}$ in degree $i$ for $z$ and $v$, then $v \in N(x)$.
--
--   This is the descent half of the comparison between the germ lattice $N(x)$ at a point $x$ of $\operatorname{Spec} B$ and the lattice of sections of $\eta_i$ over the geometric fibre at $x$: a section over the fibre forces its coordinate vector to lie already in $N(x)$, with no denominator lost. It is the substantial direction of the two equivalences `mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq` and `mem_iff_exists_isEtaSection_one_map_of_isAlgClosed_of_ker_eq`, in degree $i = 0$ and $i = 1$ respectively.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
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
    ∀ (x' : PrimeSpectrum L) (v : Fin 2 → ℚ_[p]),
      (∃ (f : L) (_ : f ∉ x'.asIdeal) (hc : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom f))
        (hcb : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom f))
        (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom f))
        (L' : _) (hL' : (((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L'),
        ∃ z, (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L' hL' i z v) →
      v ∈ N x := by sorry
