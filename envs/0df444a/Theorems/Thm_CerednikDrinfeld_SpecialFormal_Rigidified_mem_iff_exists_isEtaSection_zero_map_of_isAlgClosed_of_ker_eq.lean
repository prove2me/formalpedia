-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/67ffe1c0-ce09-59a2-95b4-26523da65e66
-- title:
--   Even η-lattice at a point equals that of the geometric fibre
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring map $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and a formal $O_D$-module $\Phi$ over $O/pO$ which is special for $\bar\jmath = \iota$ followed by reduction (its Lie algebra splits into complementary invertible weight-$0$ and weight-$1$ parts), has height $4$, satisfies $\Phi.\mathrm{lieZero}(\bar\jmath) \subseteq \ker \Phi.\mathrm{lieVarpi}$, and whose Cartier module has complementary graded pieces of weights $0$ and $1$ (`hcΦ`), so that `toGradedCartierModuleData` is available; let $r_\Phi : \mathbb{Z}_p^2 \to$ its $N$-module be additive, assume a canonical $L$-map exists for this data and that for every canonical $L$-map $L$ the map $r_\Phi$ is a bijection from all of $\mathbb{Z}_p^2$ onto the even $\eta$-piece `etaPiece L _ 0`. Let $B$ be a noetherian $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi : O \to B$, and $t = (X, n, \rho)$ a rigidified object over $B$ admissible for $(\iota,\psi)$, i.e. $X$ special for the structure map, of height $4$, and $\rho$ an isogeny $\bar\Phi \to \bar X$ of height $4n$. Let $N_0$ assign to each point of $\operatorname{Spec} B$ a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$, characterised by `hN₀`: $v \in N_0(x)$ exactly when there are $f \notin \mathfrak{p}_x$, gradedness data for $X$, for its reduction and for the base-changed $\bar\Phi$ over $B_f$, a canonical $L$-map $L$ on the graded Cartier data of $X_{B_f}$, and $z$ with $\mathrm{IsEtaSection}\,\dots\,0\,z\,v$ (so $z$ lies in the even $\eta$-piece and its reduction satisfies the lattice relation with $r_\Phi$ transported to $\bar X_{B_f}$). Finally let $K$ be an algebraically closed field that is a $\mathbb{Z}_p$-algebra, $g : B \to K$ a ring map compatible with the $\mathbb{Z}_p$-structures, $x$ the point of $\operatorname{Spec} B$ with $\ker g = \mathfrak{p}_x$, and assume $t$ base-changed along $g$ is admissible for $(\iota, g\circ\psi)$. Then for every point $x'$ of $\operatorname{Spec} K$ and every $v \in \mathbb{Q}_p^2$: $v \in N_0(x)$ if and only if there are $f \notin \mathfrak{p}_{x'}$, gradedness data over $K_f$, a canonical $L$-map $L'$ there, and $z$ with $\mathrm{IsEtaSection}$ for $t$ base-changed along $g$ at index $0$ witnessing $v$.
--
--   This identifies the even part of the $\eta$-lattice attached to a point $x$ of $\operatorname{Spec} B$ with the even $\eta$-lattice computed on the geometric fibre at $x$; it is the base-change invariance (constructibility) statement for Drinfeld's $\eta$ in the Čerednik–Drinfeld uniformisation package, in the form used to reduce statements about the lattice datum over a noetherian base to statements over algebraically closed fields. It is cited in the proofs that the relevant stalk maps are surjective, that tangent germs can be written as multiples, and that the determinant index vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.mem_iff_exists_isEtaSection_zero_map_of_isAlgClosed_of_ker_eq
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
    (N₀ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)

    {L : Type} [Field L] [IsAlgClosed L] [Algebra ℤ_[p] L] (g : B →+* L)
    (hg : g.comp (algebraMap ℤ_[p] B) = algebraMap ℤ_[p] L)
    (x : PrimeSpectrum B) (hx : RingHom.ker g = x.asIdeal)
    (ht' : (t.map g).IsAdmissible ι (g.comp ψ)) :
    ∀ (x' : PrimeSpectrum L) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
      ∃ (f : L) (_ : f ∉ x'.asIdeal) (hc : (t.map g).IsGradedS ι (g.comp ψ) (Rigidified.awayHom f))
        (hcb : (t.map g).IsGradedSbar ι (g.comp ψ) (Rigidified.awayHom f))
        (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι (g.comp ψ) (Rigidified.awayHom f))
        (L' : _) (hL' : (((t.map g).XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L'),
        ∃ z, (t.map g).IsEtaSection ι hcΦ rΦ (g.comp ψ) ht'.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L' hL' 0 z v := by sorry
