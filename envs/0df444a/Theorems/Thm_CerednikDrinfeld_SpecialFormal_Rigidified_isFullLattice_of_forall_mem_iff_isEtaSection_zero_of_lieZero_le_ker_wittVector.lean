-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/9e88886a-7d93-5fa4-a036-d06505e0cc45
-- title:
--   The η₀-period stalks N₀(x) are full ℤₚ-lattices
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$, with structure character $\bar{\jmath} = \iota$ followed by reduction modulo $p$. Assume: $\Phi$ is special for $\bar{\jmath}$ (its Lie algebra is the direct sum of the two eigenspace submodules `lieZero` and `lieOne`, each invertible); $\Phi$ has height $4$, i.e. the kernel of the action of $p$ has degree $p^4$; `lieZero` is contained in the kernel of the endomorphism of the Lie algebra induced by $\varpi$; the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary, giving graded Cartier module data $D_\Phi$; $r_\Phi : \mathbb{Z}_p^2 \to (D_\Phi)^{\mathrm{NMod}}$ is an additive map; a canonical $L$-map for $D_\Phi$ exists; and for every canonical $L$-map $L$ the map $r_\Phi$ carries all of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $D_\Phi$ for $L$. Let further $B$ be a Noetherian commutative $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : W(k) \to B$ a ring homomorphism, and $t = (X, n, \rho)$ a rigidified object over $B$ which is admissible for $(\iota, \psi)$: $X$ is special for $\psi \circ \iota$ and of height $4$, and $\rho$ is an isogeny from $\bar\Phi$ to $\bar X$ of height $4n$. Finally let $N_0$ assign to each point $x$ of $\operatorname{Spec} B$ a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$, subject to the hypothesis that $v \in N_0(x)$ holds exactly when there is an $f \notin x$ such that, over the localisation $B_f$, the graded pieces of the Cartier modules of $X$, of $\bar X$ and of $\bar\Phi$ are complementary in degrees $0$ and $1$, and there are a canonical $L$-map $L$ for the resulting data and an element $z$ with `IsEtaSection … 0 z v`, i.e. $z$ lies in the degree-$0$ $\eta$-piece for $L$ and the image of $z$ under the reduction map to the data of $\bar X$ over $B_f$ stands in the relation `LatticeRel` (in level $n$, with respect to the rigidified comparison map built from $r_\Phi$, base change and $\rho$) to $v$. The conclusion is that for every point $x$ of $\operatorname{Spec} B$ the module $N_0(x)$ is a full lattice: it is finitely generated over $\mathbb{Z}_p$ and its $\mathbb{Q}_p$-span is all of $\mathbb{Q}_p^2$.
--
--   This is the finiteness-and-nondegeneracy statement for the period module attached, at each point of $\operatorname{Spec} B$, to the degree-$0$ $\eta$-sections of an admissible rigidified special formal $\mathcal{O}_D$-module, in the Čerednik–Drinfeld uniformisation of the relevant formal moduli problem. It is used in the construction of a submodule whose members are precisely the $\eta$-sections and which is a full lattice, the input to the lattice-tree description of the uniformising space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isFullLattice_of_forall_mem_iff_isEtaSection_zero_of_lieZero_le_ker_wittVector
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
    ∀ x : PrimeSpectrum B, LT.LatticeTree.IsFullLattice (N₀ x) := by sorry
