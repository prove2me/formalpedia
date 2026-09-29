-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_add_of_isAdmissible
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_add_of_isAdmissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/9fa750a9-7000-512e-b94a-d3fb1e731398
-- title:
--   Sums of η-presented vectors at a point of Spec B
-- statement:
--   Fix a prime $p$, a commutative ring $O$ and a ring homomorphism $\iota\colon \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $O/pO$ (a two-dimensional commutative formal group law with an action of $\mathbb{W}(\mathbb{F}_{p^2})$ and a $\varpi$ with $\varpi\circ\varpi = [p]$). Assume $\Phi$ is special for `Rigidified.jbar ι`, the reduction $\iota$ followed by $O \to O/pO$, that $\Phi$ has height $4$ (the kernel of $[p]$ has degree $p^4$), and that the graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary, with witness `hcΦ`; let $\Phi$'s graded Cartier datum be $D_\Phi$. Given an additive map $r_\Phi\colon \mathbb{Z}_p^2 \to (D_\Phi).\mathrm{NMod}$, assume a canonical $L$-map on $D_\Phi$ exists and that for every canonical $L$-map $L$ the map $r_\Phi$ is a bijection of $\mathbb{Z}_p^2$ onto the degree-$0$ $\eta$-piece of $L$. Let $B$ be a Noetherian commutative $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi\colon O \to B$ a ring homomorphism, and $t = (X, n, \rho)$ a rigidified datum over $B$ that is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, $X$ has height $4$, and $\rho$ is an isogeny $\bar\Phi \to \bar X$ of height $4n$. Then for every point $x \in \operatorname{Spec} B$, every $i \in \{0,1\}$ and all $v, v' \in \mathbb{Q}_p^2$, if each of $v$ and $v'$ is presented at $x$ in degree $i$ — meaning there are $f \notin x$, complementarity witnesses grading the Cartier modules of $X$, of $\bar X$ and of $\bar\Phi$ over the localisation $B[1/f]$, a canonical $L$-map $L$ on the graded Cartier datum of $X_{B[1/f]}$, and an element $z$ of its degree-$i$ $\eta$-piece whose image under $\varpi_N^{\,i}$ and reduction is related to $p^i v$ by the lattice relation via `rigidNum` with shift $n$ — then $v + v'$ is presented at $x$ in degree $i$ in the same sense.
--
--   This is the additive closure step in the proof that the $\eta$-stalks attached to an admissible rigidified formal $O_D$-module are $\mathbb{Z}_p$-lattices in $\mathbb{Q}_p^2$, the Cartier-theoretic heart of the Čerednik–Drinfeld description of the $p$-adic uniformisation of Shimura curves. It is used by the statement that the presented vectors at a point form a submodule characterised by the $\eta$-section condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_add_of_isAdmissible.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_add_of_isAdmissible
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
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∀ (x : PrimeSpectrum B) (i : Fin 2) (v v' : Fin 2 → ℚ_[p]),
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
          (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v) →
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
          (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z v') →
      ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
        (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
        (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
        ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL i z (v + v') := by sorry
