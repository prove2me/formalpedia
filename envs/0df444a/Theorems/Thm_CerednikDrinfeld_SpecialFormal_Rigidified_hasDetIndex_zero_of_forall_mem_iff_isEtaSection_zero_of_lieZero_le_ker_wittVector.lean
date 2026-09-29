-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/fd2fc471-de66-5ea7-a706-4d2b49d43bd5
-- title:
--   Determinant index 0 of N₀(𝔭) on the critical stratum
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : W(\mathbb F_{p^2}) \to W(k)$ a ring map. Let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/pW(k)$, with $\bar\jmath = \iota$ followed by reduction mod $p$, subject to: $\Phi$ is special for $\bar\jmath$ (its Lie algebra is the direct sum of the complementary invertible submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$, the eigenspaces for the $W(\mathbb F_{p^2})$-action with characters $\bar\jmath$ and $\bar\jmath\circ\sigma$); $\Phi$ has height $4$; $\mathrm{lieZero}$ is killed by the linear part $\mathrm{lieVarpi}$ of $\varpi$; the degree-$0$ and degree-$1$ Teichmüller eigenpieces of the Cartier module of $\Phi$ are complementary, giving graded Cartier module data $D_\Phi$; $rΦ : \mathbb Z_p^2 \to D_\Phi.\mathrm{NMod}$ is additive; a canonical $L$-map for $D_\Phi$ exists; and for every canonical $L$-map $L$, $rΦ$ maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\mathrm{etaPiece}\,L\,0$. Let $B$ be a Noetherian commutative $\mathbb Z_p$-algebra with $p$ nilpotent, $\psi : W(k) \to B$, and $t = (X, n, \rho)$ a rigidified object over $B$ admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, of height $4$, and $\rho$ is an isogeny $\bar\Phi \to \bar X$ of height $4n$. Let $N_0$ assign to each $x \in \operatorname{Spec} B$ a $\mathbb Z_p$-submodule of $\mathbb Q_p^2$, characterised by: $v \in N_0(x)$ iff for some $f \notin x$ the three graded-complementarity conditions hold over $B_f$ and, for some canonical $L$-map $L$ there and some $z$, the pair $(z,v)$ is a degree-$0$ $\eta$-section in the sense of `IsEtaSection`. Then for every prime $x$ with $\mathrm{lieVarpi}(\mathrm{lieZero}(X)) \subseteq x \cdot \mathrm{lieOne}(X)$, the lattice $N_0(x)$ has determinant index $0$ for $p$: some $g \in GL_2(\mathbb Q_p)$ carries $\mathbb Z_p^2$ onto $N_0(x)$ and has $\det g$ a unit of $\mathbb Z_p$.
--
--   This is the determinant-index computation for the $\eta$-lattice attached to a rigidified special formal $O_D$-module at a point of the critical stratum, over the base ring $W(k)$ with $k$ algebraically closed, in the Čerednik–Drinfeld uniformisation of the Deligne formal upper half-plane. It is used downstream in the local-constancy statement for $N_0$ on an open neighbourhood and in the construction of the full-lattice datum from an admissible rigidified object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.hasDetIndex_zero_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
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
