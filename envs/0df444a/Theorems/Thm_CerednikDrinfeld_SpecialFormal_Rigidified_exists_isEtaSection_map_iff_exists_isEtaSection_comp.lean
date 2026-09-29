-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_iff_exists_isEtaSection_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/9bb5af5c-9d89-5304-a098-acb957036a2c
-- title:
--   Existence of η-sections is stable under re-indexing base change
-- statement:
--   Fix a prime $p$ and a commutative ring $O$ with a ring homomorphism $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and let $\Phi$ be a formal $O_D$-module over $O/pO$ whose Cartier module, graded by the Teichmüller eigenvalue conditions relative to $\bar{\jmath} = \iota$ followed by reduction mod $p$, has complementary pieces in degrees $0$ and $1$ (the hypothesis `hcΦ`); let $r_\Phi$ be an additive map from $\mathbb{Z}_p^2$ to the $N$-module of the resulting graded Cartier module data for $\Phi$. Let $\psi : O \to B$ be a ring homomorphism, $t = (X, n, \rho)$ a rigidified object over $B$, with `hOD` asserting that $\rho$ is a homomorphism of formal $O_D$-modules from $t.\bar\Phi_\psi$ to $\bar X$, let $g_0 : B \to B'$ be a ring homomorphism, `hOD'` the same assertion for the base change $t.\mathrm{map}\ g_0$ over $B'$ with structure map $g_0 \circ \psi$, let $h : B' \to S$ be a ring homomorphism, $i \in \{0,1\}$ and $v \in \mathbb{Q}_p^2$. Then the following are equivalent: there are complementation witnesses for the gradings of $X \otimes_{B'} S$, of its reduction mod $p$ and of the base change of $\Phi$ to $S/pS$, a canonical $L$-map $L$ and an element $z$ of the corresponding $N$-module such that `IsEtaSection` holds for $t.\mathrm{map}\ g_0$ along $h$ with data $(\iota, h_{c\Phi}, r_\Phi, g_0 \circ \psi, L, i, z, v)$, namely $z$ lies in the $i$-th $\eta$-piece of $L$ and the lattice relation $\exists\, m, k, w$ with $p^m \cdot (p^i v) = w$ in $\mathbb{Q}_p^2$ and $p^k \cdot r(w) = p^{k+n+m} \cdot \bar z$ holds for the reduction of $\varpi^i z$ and the rigidifying map $r$ built from $r_\Phi$; or the same data exist for $t$ itself along the composite $h \circ g_0$.
--
--   This is the re-indexing invariance in the Čerednik–Drinfel'd part of the formalisation: the $\eta$-section condition for a rigidified special formal $O_D$-module depends only on the composite ring map to $S$, not on whether it is factored through an intermediate base change $B \to B' \to S$. It is used by the two statements identifying $\eta$-sections of a stalk with those of a fibre, [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_of_isEtaSection_of_isAlgClosed_of_ker_eq`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_of_isEtaSection_of_isAlgClosed_of_ker_eq) and [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_of_mem_of_isAlgClosed_of_ker_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_map_iff_exists_isEtaSection_comp.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_map_iff_exists_isEtaSection_comp
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    {B' : Type} [CommRing B'] (g₀ : B →+* B')
    (hOD' : FormalODModule.IsODHom ((t.map g₀).Φbar (g₀.comp ψ)) (t.map g₀).Xbar (t.map g₀).ρ)
    {S : Type} [CommRing S] (h : B' →+* S) (i : Fin 2) (v : Fin 2 → ℚ_[p]) :
    (∃ (hc : (t.map g₀).IsGradedS ι (g₀.comp ψ) h) (hcb : (t.map g₀).IsGradedSbar ι (g₀.comp ψ) h)
        (hcΦh : Rigidified.IsGradedPhiS (Φ := Φ) ι (g₀.comp ψ) h)
        (L : _) (hL : (((t.map g₀).XS h).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
        ∃ z, (t.map g₀).IsEtaSection ι hcΦ rΦ (g₀.comp ψ) hOD' h hc hcb hcΦh L hL i z v) ↔
    (∃ (hc : t.IsGradedS ι ψ (h.comp g₀)) (hcb : t.IsGradedSbar ι ψ (h.comp g₀))
        (hcΦh : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (h.comp g₀))
        (L : _) (hL : ((t.XS (h.comp g₀)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
        ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (h.comp g₀) hc hcb hcΦh L hL i z v) := by sorry
