-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/02169104-cb20-5331-a247-437c4f3ce84c
-- title:
--   Eta-sections cut out ℤₚ-submodules of ℚₚ²
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$ and a formal $\mathcal{O}$-module $\Phi$ over $W(k)/pW(k)$, with structure character $\bar\jmath$ given by $\iota$ followed by reduction mod $p$. Assume: $\Phi$ is special for $\bar\jmath$, i.e. its Lie algebra is the direct sum of the eigenspace where $\mathcal{O}$ acts through $\bar\jmath$ and the one where it acts through $\bar\jmath\circ\sigma$, both invertible modules; the kernel of multiplication by $p$ on $\Phi$ has degree $p^4$; the first of these eigenspaces lies in the kernel of the linear part of $\varpi$; the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary ($h_{c\Phi}$), so that the graded Cartier module data and its quotient $N$-module are defined; $r_\Phi : \mathbb{Z}_p^2 \to N(M_\Phi)$ is additive; a canonical $L$-map on $M_\Phi$ exists; and for every canonical $L$-map $L$, $r_\Phi$ carries $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\eta(L)\cap N_0$ of $N(M_\Phi)$. Let $B$ be a Noetherian $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : W(k)\to B$ a ring homomorphism, and $t=(X,n,\rho)$ a rigidified object over $B$ admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, the kernel of multiplication by $p$ on $X$ has degree $p^4$, and $\rho$ is an isogeny of height $4n$ from $\bar\Phi_\psi$ to $\bar X$. The conclusion asserts the existence of two families $N_0,N_1$ of $\mathbb{Z}_p$-submodules of $\mathbb{Q}_p^2$, indexed by $\operatorname{Spec} B$, such that for each prime $x$, each $i\in\{0,1\}$ and each $v\in\mathbb{Q}_p^2$, membership $v\in N_i(x)$ holds precisely when there are $f\notin x$, complementarity data for the degree-$0$ and degree-$1$ graded pieces of the Cartier modules of $X$, of $\bar X$ and of $\bar\Phi_\psi$ over the localisation $B_f$, a canonical $L$-map $L$ for the graded Cartier module data of $X$ over $B_f$, and an element $z$ of the corresponding $N$-module satisfying `IsEtaSection` in degree $i$ for $v$, that is: $z$ lies in $\eta(L)\cap N_i$, and, writing $\bar z$ for the reduction to $N(M_{\bar X_f})$ of $\varpi_N^{\,i}z$, there are $m,k\in\mathbb{N}$ and $w\in\mathbb{Z}_p^2$ with $p^m\cdot(p^i v)=w$ in $\mathbb{Q}_p^2$ and $p^k\cdot r(w)=p^{k+n+m}\cdot\bar z$, where $r$ is the rigidifying map obtained from $r_\Phi$ by base change along $\psi$ and $f$ and by $\rho$. Thus each of these two sets of $v$ is a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$.
--
--   This is the submodule step in the construction of the $p$-adic period lattices attached to an admissible rigidified special formal $\mathcal{O}$-module in the Čerednik–Drinfeld uniformisation: the sets of rational coordinate vectors realised by $\eta$-sections in degrees $0$ and $1$, taken stalkwise over $\operatorname{Spec} B$, are closed under addition and under scaling by $\mathbb{Z}_p$. It is used by the refinement asserting in addition that these submodules are full lattices in $\mathbb{Q}_p^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_submodule_forall_mem_iff_isEtaSection_of_isAdmissible_of_lieZero_le_ker_wittVector
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
    ∃ (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p])),
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v) := by sorry
