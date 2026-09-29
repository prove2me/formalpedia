-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/369dfc36-082d-54e6-bee9-1328a883b725
-- title:
--   Germs of the tangent stalk maps come from single sections
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring homomorphism $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and a formal $\mathcal{O}_D$-module $\Phi$ of dimension $2$ over $O/pO$; write $\bar\jmath$ for $\iota$ followed by reduction. Assume $\Phi$ is special for $\bar\jmath$ (its Lie algebra is the direct sum of the two eigen-submodules $\mathrm{lieZero}$, $\mathrm{lieOne}$, both invertible), has height $4$, and that the graded pieces $0$ and $1$ of its Cartier module are complementary, giving a graded Cartier datum; let $r_\Phi : \mathbb{Z}_p^2 \to N$ be an additive map into its $N$-module, assume a canonical $L$-map exists and that for every canonical $L$ the map $r_\Phi$ is a bijection of $\mathbb{Z}_p^2$ onto the $\eta$-piece of degree $0$. Let $B$ be a Noetherian $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi : O \to B$ a ring homomorphism, and $t = (X,n,\rho)$ a rigidified triple over $B$ that is admissible for $\iota,\psi$ ($X$ special for $\psi\circ\iota$ of height $4$, and $\rho$ an isogeny $\bar\Phi \to \bar X$ of height $4n$). Let $N_0, N_1$ assign to each point $x$ of $\mathrm{Spec}\,B$ a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$, characterised by: $v \in N_i(x)$ if and only if there are $f \notin x$, complementarity data for the graded pieces of $X$, of $\bar X$ and of $\bar\Phi$ over $B_f$, a canonical $L$ for the datum of $X$ over $B_f$, and an element $z$ which is an $\eta$-section of degree $i$ for $v$ (that is, $z$ lies in the $\eta$-piece of degree $i$ and $\varpi^i z$, reduced and compared with the rigidification $r_\Phi$ transported along $\rho$, satisfies the lattice relation with $p^i v$). Assume each $N_i(x)$ is a full lattice (finitely generated and spanning $\mathbb{Q}_p^2$), $N_0(x) \le N_1(x)$, and $p\,N_1(x) \subseteq N_0(x)$. Let $\Pi_0, \Pi_1$ be $B$-linear maps between $\mathrm{lieZero}$ and $\mathrm{lieOne}$ of $X$ inducing on underlying vectors the linear part of the $\varpi$-action on $\mathrm{Lie}\,X$. Finally let $u_i(x) : B_x \otimes_{\mathbb{Z}_p} N_i(x) \to (\mathrm{Lie}\,X)_{i,x}$ be $B_x$-linear maps satisfying the germ clauses: for every presentation $(f, L, z)$ of $v \in N_i(x)$ there are $m$ in the Cartier module of $X$ over $B_f$, a section $s$ of the $i$-th Lie piece and $b \notin x$ such that the class of $m$ modulo the image of Verschiebung is the image of $z$ under the map attached to $L$, $u_i(x)(1 \otimes v) = s/b$, and each coordinate satisfies $s_i = b\cdot \mathrm{tangent}(m)_i$ in $B_x$. The conclusion is that for $i = 0, 1$, each point $x$ and each $v \in N_i(x)$, there are $f \notin x$ and a global section $s$ of the $i$-th Lie piece such that for every point $y$ with $f \notin y$ one has $v \in N_i(y)$ and $u_i(y)(1 \otimes v) = s/f$ in the stalk at $y$.
--
--   This is the statement that the pointwise maps $u_i$ on tangent germs are the stalks of a morphism of sheaves on $\mathrm{Spec}\,B$: a single quotient $s/f$ represents $u_i(1\otimes v)$ simultaneously on the basic open set $D(f)$, the denominators being controlled because $B$ is Noetherian. It feeds the construction of the lattice-tree point attached to an admissible rigidified special formal module, used in the Čerednik–Drinfeld uniformisation input to the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_stalkMap_tmul_eq_mk_of_tangent_germ
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
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
    (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v)
    (hN₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v)
    (hfull₀ : ∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) (hfull₁ : ∀ x, LT.LatticeTree.IsFullLattice (N₁ x))
    (hle : ∀ x, N₀ x ≤ N₁ x) (hsmul : ∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x)
    (Pi₀ : ↥(t.X.lieZero (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) (Pi₁ : ↥(t.X.lieOne (structureMap ι ψ)) →ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (hPi₀ : ∀ s : ↥(t.X.lieZero (structureMap ι ψ)), ((Pi₀ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (hPi₁ : ∀ s : ↥(t.X.lieOne (structureMap ι ψ)), ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie))
    (u₀ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))
    (u₁ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)))
    (hg₀ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieZero (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)))
    (hg₁ :
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]) (hv : v ∈ N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (Rigidified.awayHom f)) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f))
          (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
          (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M) (s : ↥(t.X.lieOne (structureMap ι ψ)))
          (b : x.asIdeal.primeCompl),
          ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, Rigidified.locHom x ((s : t.X.Lie) i) =
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i))) :
    (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x →
          ∃ (f : B) (s : ↥(t.X.lieZero (structureMap ι ψ))), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
            ∃ hv : v ∈ N₀ y, u₀ y ((1 : FormalOmega.locRing B y) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ y))) = LocalizedModule.mk s ⟨f, hy⟩) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x →
          ∃ (f : B) (s : ↥(t.X.lieOne (structureMap ι ψ))), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
            ∃ hv : v ∈ N₁ y, u₁ y ((1 : FormalOmega.locRing B y) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ y))) = LocalizedModule.mk s ⟨f, hy⟩) := by sorry
