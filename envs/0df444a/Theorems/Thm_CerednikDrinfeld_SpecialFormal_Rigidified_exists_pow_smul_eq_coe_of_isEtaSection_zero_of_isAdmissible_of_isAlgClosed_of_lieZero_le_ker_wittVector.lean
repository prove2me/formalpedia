-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/119286f0-7913-56f5-aded-382119c2e3d2
-- title:
--   Bounded denominators for degree-zero η-periods over a geometric fibre
-- statement:
--   Let $p$ be a prime, let $k$ be an algebraically closed field of characteristic $p$, and let $\iota$ be a ring homomorphism from $W(\mathbb{F}_{p^2})$ to the Witt vectors $W(k)$; write $\bar{\jmath}$ for $\iota$ followed by the quotient map $W(k)\to W(k)/pW(k)$. Let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/pW(k)$ which is special for $\bar{\jmath}$ (its Lie algebra is the direct sum of the invertible eigenpieces $\mathrm{lieZero}$ and $\mathrm{lieOne}$) and of height $4$ (the kernel of the action of $p$ has degree $p^4$), and assume $\mathrm{lieZero}(\bar{\jmath})$ is annihilated by the linear part of $\varpi$ on the Lie algebra, and that the graded pieces $0$ and $1$ of the Cartier module of $\Phi$ are complementary, via `hcΦ`. Let $r_\Phi\colon \mathbb{Z}_p^2\to N$ be an additive map into the $N$-module of the associated graded Cartier module data, assume a canonical $L$-map exists there, and assume that for every canonical $L$-map $L$ the map $r_\Phi$ is a bijection from all of $\mathbb{Z}_p^2$ onto the degree-$0$ piece $\eta(L)\cap N_0$. Let $B$ be an algebraically closed field which is a $\mathbb{Z}_p$-algebra with $p$ nilpotent, let $\psi\colon W(k)\to B$ be a ring homomorphism, and let $t=(X,n,\rho)$ be a rigidified object over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$ and of height $4$, and $\rho$ is an isogeny of height $4n$ from the base change of $\Phi$ to the reduction of $X$. Then for every point $x$ of $\operatorname{Spec} B$ there is an exponent $b\in\mathbb{N}$ such that every $v\in\mathbb{Q}_p^2$ which is realised in degree $0$ at $x$ satisfies $p^b\cdot v\in\mathbb{Z}_p^2$, coordinatewise. Here $v$ is realised at $x$ when for some $f\notin x$, complementarity of the graded pieces $0$ and $1$ over the localisation $B_f$ for $X$, for its reduction and for the base change of $\Phi$, some canonical $L$-map $L$ there, and some $z$ lying in $\eta(L)\cap N_0$, the reduction of $z$ along $\rho$ and the rigidification satisfy the lattice relation: there are $m,k\in\mathbb{N}$ and $w\in\mathbb{Z}_p^2$ with $p^m\cdot v=w$ and $p^k\cdot r(w)=p^{k+n+m}\cdot \bar z$, where $r$ is the composite of $r_\Phi$ with the base change and $\rho$-maps on $N$-modules. The bound $b$ is uniform in $v$ and in all the auxiliary choices $f$, $L$ and $z$.
--
--   This is the geometric-fibre case of the bounded-denominators statement for the rigidified coordinates of degree-zero $\eta$-sections in the Cartier-theoretic description of special formal $O_D$-modules, which underlies the Čerednik–Drinfeld uniformisation. It is cited by [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_lieZero_le_ker_wittVector), where the base ring is no longer assumed to be an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector
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
    {B : Type} [Field B] [IsAlgClosed B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∀ x : PrimeSpectrum B, ∃ b : ℕ, ∀ v : Fin 2 → ℚ_[p],
      (∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
          (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) →
      ∃ w : Fin 2 → ℤ_[p], (p : ℚ_[p]) ^ b • v = fun j => ((w j : ℤ_[p]) : ℚ_[p]) := by sorry
