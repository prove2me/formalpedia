-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/b920c089-2ef8-5c79-9ba6-de4e56893543
-- title:
--   Uniformly bounded denominators for degree-zero η-sections at a prime
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota : \mathbb{W}(p,\mathbb{F}_{p^2}) \to \mathbb{W}(p,k)$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $\mathbb{W}(p,k)/p\mathbb{W}(p,k)$, with $\bar\jmath$ the composite of $\iota$ with reduction modulo $p$. Assume: $\Phi$ is special for $\bar\jmath$, i.e. its Lie algebra is the direct sum of the eigenspaces $\mathrm{lieZero}$ and $\mathrm{lieOne}$ and both are invertible modules; $\Phi$ has height $4$ (the kernel of multiplication by $p$ has degree $p^4$); $\mathrm{lieZero}\,\bar\jmath$ is contained in the kernel of the linear part of $\varpi$; the graded pieces of index $0$ and $1$ of the Cartier module of $\Phi$ are complementary, giving graded Cartier data $D_\Phi$; there is an additive map $r_\Phi : \mathbb{Z}_p^2 \to N(D_\Phi)$ which, for every canonical $L$-map $L$ on $D_\Phi$, maps the whole of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$. Let $B$ be a Noetherian $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, let $\psi : \mathbb{W}(p,k) \to B$ be a ring homomorphism, and let $t = (X,n,\rho)$ be a rigidified object over $B$ that is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from the base change of $\Phi$ to $\bar X$. Then for every prime $x$ of $B$ there is $b \in \mathbb{N}$ such that for every $v \in \mathbb{Q}_p^2$ the following holds: if there exist $f \notin x$, complementarity data for the graded pieces of $X$, of $\bar X$ and of the base-changed $\Phi$ over the localisation $B[1/f]$, a canonical $L$-map $L$ for the graded Cartier data of $X$ over $B[1/f]$, and an element $z$ of the corresponding $N$-module with $\mathrm{IsEtaSection}$ holding at index $0$ for $z$ and $v$ — that is, $z$ lies in the degree-$0$ $\eta$-piece of $L$ and, for some $m,k \in \mathbb{N}$ and $w \in \mathbb{Z}_p^2$, one has $p^m v = w$ and $p^k r(w) = p^{k+n+m}$ times the reduction of $z$, where $r$ is the composite of $r_\Phi$ with the base-change and $\rho$-induced maps — then there is $w \in \mathbb{Z}_p^2$ with $p^b v = w$ in $\mathbb{Q}_p^2$.
--
--   This is the denominator bound in the Čerednik–Drinfeld period comparison: the vectors of $\mathbb{Q}_p^2$ realised by degree-zero $\eta$-sections over some neighbourhood of a given prime of $B$ lie in a fixed lattice $p^{-b}\mathbb{Z}_p^2$. It feeds the construction of the submodule of such vectors and the proof that this submodule is a full lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector
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
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∀ x : PrimeSpectrum B, ∃ b : ℕ, ∀ v : Fin 2 → ℚ_[p],
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
          (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) →
      ∃ w : Fin 2 → ℤ_[p], (p : ℚ_[p]) ^ b • v = fun j => ((w j : ℤ_[p]) : ℚ_[p]) := by sorry
