-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_stalkMap_tangent_germ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/d2bc379b-85e3-527e-bbb8-7949ff18b2b9
-- title:
--   Existence of the tangent-germ stalk maps u₀,u₁
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring map $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to O$, and a formal $\mathcal{O}_D$-module $\Phi$ of dimension $2$ over $O/pO$, taken with respect to the induced map $\bar j = \mathrm{jbar}\,\iota$ into $O/pO$. Assume: $\Phi$ is special, i.e. $\mathrm{Lie}\,\Phi = (O/pO)^2$ is the direct sum of the complementary invertible submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$; $\Phi$ has height $4$, i.e. $\Phi$'s action of $p$ has kernel of degree $p^4$; the linear part $\mathrm{lieVarpi}$ of $\varpi$ kills $\mathrm{lieZero}$; the graded pieces $0$ and $1$ of the Cartier module of $\Phi$ (elements transforming under $\mathrm{teichmuller}\,c$, $c \in \mathbb{F}_{p^2}$, by the homothety $\bar j(\mathrm{teichmuller}\,c)^{p^n}$) are complementary, giving a graded Cartier datum; $r_\Phi : \mathbb{Z}_p^2 \to N$ is an additive rigidification of that datum; a canonical $L$-map for the datum exists; and for every canonical $L$, $r_\Phi$ maps $\mathbb{Z}_p^2$ bijectively onto the $\eta$-piece of $L$ in degree $0$. Let $B$ be a Noetherian $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi : O \to B$ a ring map, and $t = (X, n, \rho)$ a rigidified triple over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for the structure map $\psi \circ \iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to $\bar X$. Let $N_0, N_1$ assign to each $x \in \operatorname{Spec} B$ a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$, characterised by: $v \in N_i(x)$ if and only if there are $f \notin x$, complementarity data for $X$, $\bar X$ and $\Phi$ over $B_f$, a canonical $L$-map $L$ and an element $z$ with $\mathrm{IsEtaSection}$ holding for $(i, z, v)$, i.e. $z$ lies in the degree-$i$ $\eta$-piece of $L$ and the reduction of $\varpi^i z$ is related to $r_\Phi$ and $p^i v$ by the lattice relation. Assume each $N_i(x)$ is a full lattice (finitely generated and spanning $\mathbb{Q}_p^2$), $N_0(x) \le N_1(x)$, and $p\,N_1(x) \subseteq N_0(x)$; let $\Pi_0, \Pi_1$ be $B$-linear maps between $\mathrm{lieZero}$ and $\mathrm{lieOne}$ of $X$ inducing $\mathrm{lieVarpi}$. Then there exist families of $B_x$-linear maps $u_0(x) : B_x \otimes_{\mathbb{Z}_p} N_0(x) \to (\mathrm{lieZero}\,X)_x$ and $u_1(x) : B_x \otimes_{\mathbb{Z}_p} N_1(x) \to (\mathrm{lieOne}\,X)_x$ such that for $i = 0, 1$, every $x$, every $v \in N_i(x)$ and every presentation $(f, L, z)$ of $v$ as above there are $m$ in the Cartier module of $X$ over $B_f$, a section $s$ of the $i$-th Lie piece over $B$ and $b \notin x$ with: the class of $m$ modulo the image of $V$ equals the value at $z$ of the datum's map $u$ attached to $L$; $u_i(x)(1 \otimes v) = s/b$ in the stalk; and in $B_x$, the image of each coordinate $s_i$ equals the image of $b$ times the image of the $i$-th tangent coordinate of $m$.
--
--   This is the construction of the stalkwise comparison maps $u_i(\mathfrak p) : B_{\mathfrak p} \otimes_{\mathbb{Z}_p} N_i(\mathfrak p) \to ((\mathrm{Lie}\,X)_i)_{\mathfrak p}$ of Boutot–Carayol II (3.13), sending a lattice vector to the germ at $\mathfrak p$ of the tangent vector of a representative of the corresponding $\eta$-section. It feeds the variant [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector), in the construction of the Čerednik–Drinfeld uniformisation from special formal $\mathcal{O}_D$-modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_stalkMap_tangent_germ
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0 : ∀ m ∈ Φ.lieZero (Rigidified.jbar ι), Φ.lieVarpi m = 0)
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
    (hPi₁ : ∀ s : ↥(t.X.lieOne (structureMap ι ψ)), ((Pi₁ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) = t.X.lieVarpi (s : t.X.Lie)) :
    ∃ (u₀ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))
      (u₁ : ∀ x : PrimeSpectrum B,
          FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
            FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ))),
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
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)) ∧
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
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)) := by sorry
