-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_of_isEtaSection_of_isAlgClosed_of_ker_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_of_isEtaSection_of_isAlgClosed_of_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/ea2db3d2-4682-5a57-b12b-ea0a150b7994
-- title:
--   Transport of an η-section to a geometric fibre
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring map $\iota : \mathbb{Z}_{p^2} \to O$, and a formal $O_D$-module $\Phi$ over $O/pO$ (a two-dimensional commutative formal group with an action of $\mathbb{Z}_{p^2}$ and a uniformiser endomorphism $\varpi$). Assume: $\Phi$ is special for $\bar\jmath = \iota$ followed by reduction mod $p$, i.e. its Lie pieces in degrees $0$ and $1$ are complementary and invertible; $\Phi$ has height $4$; the graded pieces `gradedPiece` of degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary, giving graded Cartier module data $D_\Phi$; $r_\Phi : \mathbb{Z}_p^2 \to (D_\Phi).\mathrm{NMod}$ is additive; a canonical $L$-map for $D_\Phi$ exists; and for every canonical $L$-map $L$ of $D_\Phi$ the map $r_\Phi$ is a bijection of $\mathbb{Z}_p^2$ onto the degree-$0$ $\eta$-piece `etaPiece` of $L$. Let $B$ be a noetherian $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : O \to B$ a ring map, and $t = (t.X, t.n, t.\rho)$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$: $t.X$ is special for the structure map, has height $4$, and $t.\rho$ is an isogeny of height $4\,t.n$ from $\bar\Phi_\psi$ to $\bar{t.X}$. Let $L$ be an algebraically closed field which is a $\mathbb{Z}_p$-algebra, $g : B \to L$ a ring map compatible with the $\mathbb{Z}_p$-structures, and $x \in \operatorname{Spec} B$ with $\ker g = \mathfrak{p}_x$, and assume the base change $t.\mathrm{map}\,g$ is admissible for $(\iota, g \circ \psi)$. Finally fix $i \in \{0,1\}$, $v \in \mathbb{Q}_p^2$, an element $f_0 \in B \setminus \mathfrak{p}_x$ together with the complementarity hypotheses for the graded pieces of the Cartier modules of $t.X$, of its reduction, and of $\bar\Phi$ over the localisation $B[1/f_0]$, a canonical $L$-map $L_0$ for the graded Cartier module data of $t.X$ over $B[1/f_0]$, and an element $z$ satisfying `IsEtaSection`: $z$ lies in the degree-$i$ $\eta$-piece of $L_0$, and `LatticeRel` holds for the reduced data with level $t.n$, numbering map `rigidNum`, the element `etaRed` of $\varpi^i z$, and the vector $p^i v$. The conclusion is that for every $x' \in \operatorname{Spec} L$ there exist $f \in L$ outside $\mathfrak{p}_{x'}$, complementarity hypotheses for the corresponding graded pieces of $t.\mathrm{map}\,g$ over $L[1/f]$, a canonical $L$-map $L'$ there, and an element $z'$ such that $t.\mathrm{map}\,g$ satisfies `IsEtaSection` for $L'$, the same index $i$ and the same vector $v$.
--
--   This is the stalk-to-fibre step in the Cerednik–Drinfeld theory of special formal $O_D$-modules: an $\eta$-presentation of the Cartier module valid on a basic open neighbourhood $D(f_0)$ of a point $x$ of the base is carried along the geometric point $g : B \to L$ to an $\eta$-presentation over the fibre. It is used in the subsequent analysis of $\eta$-sections in degree $0$, where the lattice relation is converted into an integrality statement for the associated vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_of_isEtaSection_of_isAlgClosed_of_ker_eq.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_of_isEtaSection_of_isAlgClosed_of_ker_eq
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
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

    {L : Type} [Field L] [IsAlgClosed L] [Algebra ℤ_[p] L] (g : B →+* L)
    (hg : g.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] L)
    (x : PrimeSpectrum B) (hx : RingHom.ker g = x.asIdeal)
    (ht' : (t.map g).IsAdmissible ι (g.comp ψ))

    (i : Fin 2) (v : Fin 2 → ℚ_[p]) (f₀ : B) (hf₀ : f₀ ∉ x.asIdeal)
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom f₀)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f₀))
    (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f₀))
    (L₀ : _) (hL₀ : ((t.XS (Rigidified.awayHom f₀)).toGradedCartierModuleData _ hc).IsCanonicalLMap L₀)
    (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f₀) hc hcb hcΦf L₀ hL₀ i z v) :
    ∀ x' : PrimeSpectrum L,
      ∃ (f : L) (_ : f ∉ x'.asIdeal) (hc' : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom f))
        (hcb' : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom f))
        (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom f))
        (L' : _) (hL' : (((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc').IsCanonicalLMap L'),
        ∃ z', (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom f) hc' hcb' hcΦf' L' hL' i z' v := by sorry
