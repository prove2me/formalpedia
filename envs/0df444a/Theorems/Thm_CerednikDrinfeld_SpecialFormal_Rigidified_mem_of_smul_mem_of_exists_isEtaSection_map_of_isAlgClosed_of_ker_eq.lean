-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/d128a73f-3a32-5581-8e71-6aaf206c5e64
-- title:
--   p-saturation of η-germ lattices at a geometric fibre
-- statement:
--   Fix a prime $p$, a commutative ring $O$, a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to O$, and a formal $O_D$-module $\Phi$ of dimension $2$ over $O/pO$; write $\bar\jmath=\iota$ followed by reduction modulo $pO$. Assume $\Phi$ is special for $\bar\jmath$ (its Lie algebra splits into complementary invertible $\bar\jmath$-eigenpieces in degrees $0$ and $1$), has height $4$, satisfies $\mathrm{lieZero}\subseteq\ker(\mathrm{lieVarpi})$, and that the degree-$0$ and degree-$1$ graded pieces of its Cartier module are complementary, giving graded Cartier module data for $\Phi$; let $r_\Phi\colon\mathbb Z_p^2\to N(\Phi)$ be additive, assume a canonical $L$-map exists for $\Phi$, and that for every canonical $L$-map $L$ the map $r_\Phi$ sends all of $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece attached to $L$. Let $B$ be a noetherian $\mathbb Z_p$-algebra in which $p$ is nilpotent, $\psi\colon O\to B$ a ring homomorphism, and $t=(X,n,\rho)$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for the structure map of $(\iota,\psi)$, has height $4$, and $\rho$ is an isogeny of height $4n$ from $\bar\Phi_\psi$ to $\bar X$. Fix $i\in\{0,1\}$ and a map $N$ assigning to each point $x\in\operatorname{Spec}B$ a $\mathbb Z_p$-submodule $N(x)\subseteq\mathbb Q_p^2$, subject to the hypothesis that $v\in N(x)$ holds exactly when there are $f\notin x$, complementarity of the graded pieces for $X$, $\bar X$ and $\bar\Phi_\psi$ over the localisation $B_f$, a canonical $L$-map $L$ there, and an element $z$ lying in the $\eta$-piece of index $i$ with $\varpi_N^i z$ reducing, through the numbering map built from $r_\Phi$ and $\rho$, into the lattice relation with $p^i v$. Let $K$ be an algebraically closed field that is a $\mathbb Z_p$-algebra, $g\colon B\to K$ a ring homomorphism compatible with the $\mathbb Z_p$-structures, $x\in\operatorname{Spec}B$ the point cut out by $\ker g$, and assume $t$ base-changed along $g$ is admissible for $(\iota,g\circ\psi)$. The assertion: for every point $x'\in\operatorname{Spec}K$ and every $v\in\mathbb Q_p^2$, if $p\,v\in N(x)$ and $v$ admits such an $\eta$-section presentation of index $i$ for the base-changed object over a localisation of $K$ away from some $f\notin x'$, then $v\in N(x)$.
--
--   This is the saturation step in the construction of the lattice of $\eta$-germs attached to a rigidified special formal module: a vector whose $p$-multiple is a germ at $x$ and which is already realised by an $\eta$-section over the geometric fibre is itself a germ at $x$. It is used by [`CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq), which transfers membership from the geometric fibre to the local ring, in the Čerednik–Drinfeld comparison between special formal modules and the Drinfeld upper half plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq
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
      algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N x →
      (∃ (f : L) (_ : f ∉ x'.asIdeal) (hc : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom f))
        (hcb : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom f))
        (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom f))
        (L' : _) (hL' : (((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L'),
        ∃ z, (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L' hL' i z v) →
      v ∈ N x := by sorry
