-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_of_isAlgClosed_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_of_isAlgClosed_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/da0bbec2-0019-5f96-a6fb-fdc92a37f503
-- title:
--   Determinant index zero at a 0-critical point over algebraically closed B
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : W(\mathbb F_{p^2}) \to W(k)$ a ring homomorphism, with $\bar\iota =$ `Rigidified.jbar ι` its composite with reduction modulo $p$. Let $\Phi$ be a formal $O_D$-module over $W(k)/pW(k)$ (a $2$-dimensional commutative formal group with a $W(\mathbb F_{p^2})$-action and an endomorphism $\varpi$ with $\varpi^2 = [p]$) such that: $\Phi$ is special for $\bar\iota$, i.e. its Lie algebra is the direct sum of the eigen-submodules `lieZero` and `lieOne`, both invertible; $\Phi$ has height $4$; `lieZero` is killed by the linear part `lieVarpi` of $\varpi$ ($0$ is critical); and the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary ($h_{c\Phi}$), so that $\Phi$ gives graded Cartier module data. Let $r_\Phi$ be an additive map from $\mathbb Z_p^2$ to the associated $N$-module, assume some canonical $L$-map exists, and assume that for every canonical $L$ the map $r_\Phi$ sends all of $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece for $L$. Let $B$ be an algebraically closed field that is a $\mathbb Z_p$-algebra with $p$ nilpotent, $\psi : W(k) \to B$ a ring homomorphism, and $t = (X, n, \rho)$ a rigidified object over $B$ admissible for $(\iota,\psi)$: $X$ is special for $\psi \circ \iota$ and of height $4$, and $\rho$ is an isogeny of height $4n$ from $\bar\Phi_\psi$ to $\bar X$. Let $N_0$ assign to each point $x$ of $\operatorname{Spec} B$ a $\mathbb Z_p$-submodule of $\mathbb Q_p^2$, and assume the membership clause: $v \in N_0(x)$ holds exactly when there are $f \notin x$, complementarity data for the graded pieces of $X$, $\bar X$ and $\bar\Phi$ over the localisation $B_f$, a canonical $L$-map for $X_{B_f}$, and an element $z$ with `IsEtaSection … 0 z v`, i.e. $z$ lies in the degree-$0$ $\eta$-piece for $L$ and its reduction along $\rho$ stands in the lattice relation `LatticeRel` with $v$ and the rigidifying map built from $r_\Phi$. Then for every point $x$ of $\operatorname{Spec} B$ such that `lieVarpi` maps the submodule `lieZero` of $\operatorname{Lie} X$ into $x \cdot$ `lieOne`, the module $N_0(x)$ has determinant index $0$ with respect to $p$: there is $g \in GL_2(\mathbb Q_p)$ with $g \cdot \mathbb Z_p^2 = N_0(x)$ and $\det g$ a unit of $\mathbb Z_p$.
--
--   This is the computation of the determinant index of the even $\eta$-lattice attached to a rigidified special formal $O_D$-module on a geometric fibre, at a base point for which $0$ is critical, in the form needed for the Čerednik–Drinfeld description of the $p$-adic upper half plane; it is the case of the stratum where the degree-$0$ index vanishes. It feeds the corresponding statement over a general base, where the algebraically closed field is obtained by passing to a geometric point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_of_isAlgClosed_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_of_isAlgClosed_wittVector
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
    (N₀ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) :
    ∀ x : PrimeSpectrum B,
      Submodule.map t.X.lieVarpi (t.X.lieZero (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieOne (structureMap ι ψ) →
      FormalOmega.HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) (N₀ x) 0 := by sorry
