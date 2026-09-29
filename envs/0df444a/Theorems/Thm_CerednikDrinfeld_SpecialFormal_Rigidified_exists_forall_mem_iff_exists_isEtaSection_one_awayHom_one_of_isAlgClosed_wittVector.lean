-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/5d556949-a2b8-5255-8942-e714bcaf58e2
-- title:
--   Degree-one η-sections over a field base via one chart
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota : W(\mathbf{F}_{p^2}) \to W(k)$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/pW(k)$, with $\bar{\jmath} = \iota$ followed by the reduction map. It is assumed that $\Phi$ is special for $\bar\jmath$ (its Lie algebra is the direct sum of the eigenspace $\mathrm{lieZero}$, where each $a$ acts by $\bar\jmath(a)$, and of $\mathrm{lieOne}$, where $a$ acts by $\bar\jmath(\sigma a)$, both invertible), that $\Phi$ has height $4$ (the kernel algebra of multiplication by $p$ has rank $p^4$), that $\mathrm{lieZero}$ is killed by the linear part of $\varpi$, and that the Teichmüller-graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary (hypothesis $h_{c\Phi}$), giving graded Cartier module data for $\Phi$. Let $r_\Phi : \mathbf{Z}_p^2 \to N(\Phi)$ be an additive map into the associated $N$-module; it is assumed that a canonical $L$-map for these data exists and that, for every canonical $L$-map $L$, $r_\Phi$ maps $\mathbf{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\eta(L) \cap N_0$. Let further $B$ be an algebraically closed field which is a $\mathbf{Z}_p$-algebra with $p$ nilpotent in $B$, let $\psi : W(k) \to B$ be a ring homomorphism, and let $t = (X, n, \rho)$ be a rigidified object over $B$ which is admissible for $(\iota,\psi)$, i.e. $X$ is special for $\psi \circ \iota$ and of height $4$, and $\rho$ is an isogeny $\bar\Phi_B \to \bar X$ of height $4n$. Finally let $N_1$ assign to each point $x \in \operatorname{Spec} B$ a $\mathbf{Z}_p$-submodule of $\mathbf{Q}_p^2$, subject to the hypothesis that $v \in N_1(x)$ holds exactly when there are some $f \notin x$, some complementarity data for the degree-$0$ and degree-$1$ pieces of the Cartier modules of $X$, of $\bar X$ and of $\bar\Phi$ over the localisation $B_f$, some canonical $L$-map $L$ there, and some $z$ with $\mathrm{IsEtaSection}\ \dots\ 1\ z\ v$, meaning that $z$ lies in the degree-$1$ $\eta$-piece $\eta(L) \cap N_1$ and that the reduction of $\varpi z$ and the vector $p\,v$ satisfy the lattice relation (for some $m,k$ and $w \in \mathbf{Z}_p^2$ with $p^m v = w$ one has $p^k\, r_\rho(w) = p^{k+n+m}$ times that reduction) defined by the rigidification map $r_\rho$ obtained from $r_\Phi$ by base change along $\psi$ and $\rho$. The conclusion is that these data may be chosen once and for all over the localisation away from $1$: there exist complementarity data $h_c$, $h_{cb}$, $h_{c\Phi 1}$ for $X$, $\bar X$ and $\bar\Phi$ over $B_1$ and a canonical $L$-map $L$ for the graded Cartier data of $X_{B_1}$ such that for every $x \in \operatorname{Spec} B$ and every $v \in \mathbf{Q}_p^2$, $v \in N_1(x)$ if and only if there is a $z$ with $\mathrm{IsEtaSection}\ \dots\ (\mathrm{awayHom}\ 1)\ h_c\ h_{cb}\ h_{c\Phi 1}\ L\ h_L\ 1\ z\ v$.
--
--   This is the degree-one part of the local description of the $\eta$-lattice attached to a special formal $O_D$-module on a geometric fibre in the Čerednik–Drinfeld uniformisation: since $B$ is a field, every basic open neighbourhood of a point is all of $\operatorname{Spec} B$, so the existential choice of a chart in the definition of $N_1$ can be replaced by the single frame $B \to B_1$. It is used in the construction of the critical map for a Cartier quadruple and in the computation of the determinant index of the resulting lattice pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_one_awayHom_one_of_isAlgClosed_wittVector
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
    ∃ (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : B))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : B)))
      (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : B)))
      (L : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).NMod)
      (hL : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).IsCanonicalLMap L),
      ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]),
        v ∈ N₁ x ↔ ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom (1 : B)) hc hcb hcΦ1 L hL 1 z v := by sorry
