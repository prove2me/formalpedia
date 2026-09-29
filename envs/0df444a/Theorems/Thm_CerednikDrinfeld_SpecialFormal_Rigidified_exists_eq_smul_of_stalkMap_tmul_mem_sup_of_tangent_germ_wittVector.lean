-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/e9ef3c2d-2a62-5662-a650-b7e62c363273
-- title:
--   Drinfeld's condition [C₂] for the tangent-germ maps
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring map $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$, subject to: $\Phi$ is special for the reduction $\bar\jmath$ of $\iota$ (its Lie algebra is the direct sum of the two eigenspaces $\mathrm{lieZero}$, $\mathrm{lieOne}$, both invertible), $\Phi$ has height $4$, $\mathrm{lieZero}\,\bar\jmath \subseteq \ker(\mathrm{lieVarpi})$, the degree-$0$ and degree-$1$ graded pieces of its Cartier module (defined by the Teichmüller eigenvalue condition) are complementary via `hcΦ`, an additive $r_\Phi : \mathbb{Z}_p^2 \to N$ into the $N$-module of the associated graded Cartier datum is given, a canonical $L$-map exists, and for every canonical $L$ the map $r_\Phi$ is a bijection of $\mathbb{Z}_p^2$ onto $\eta_0(L)$. Let $B$ be a Noetherian $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi : W(k) \to B$ a ring map, and $t = (X,n,\rho)$ a rigidified triple over $B$ that is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from $\bar\Phi_\psi$ to $\bar X$. Let $N_0, N_1$ assign to each $x \in \operatorname{Spec} B$ a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$, characterised by the clause that $v \in N_i(x)$ exactly when there are $f \notin x$, splittings `IsGradedS`, `IsGradedSbar`, `IsGradedPhiS` for the localisation away from $f$, a canonical $L$ and a $z$ with `IsEtaSection` of degree $i$ relating $z$ and $v$; assume each $N_i(x)$ is a full lattice (finitely generated and spanning $\mathbb{Q}_p^2$), $N_0(x) \le N_1(x)$, and $p\,N_1(x) \subseteq N_0(x)$. Let $\Pi_0 : \mathrm{Lie}_0 X \to \mathrm{Lie}_1 X$ and $\Pi_1 : \mathrm{Lie}_1 X \to \mathrm{Lie}_0 X$ be $B$-linear maps each induced by `lieVarpi`, and for each $x$ let $u_i(x) : B_x \otimes_{\mathbb{Z}_p} N_i(x) \to (\mathrm{Lie}_i X)_x$ be $B_x$-linear maps satisfying the germ clauses `hg₀`, `hg₁`: for every presentation $(f,L,z)$ of $v \in N_i(x)$ there are $m$ in the Cartier module away from $f$, a section $s$ of $\mathrm{Lie}_i X$ and $b \notin x$ with $m$ mod $VM$ equal to $u(L)(z)$, with $u_i(x)(1 \otimes v) = s/b$, and with $s_j = b \cdot \mathrm{tangent}(m)_j$ in $B_x$ for each coordinate $j$. The conclusion is the conjunction: for all $x$ and $v \in N_0(x)$, if $u_0(x)(1\otimes v)$ lies in the image of the localisation of $\Pi_1$ plus $x\cdot(\mathrm{Lie}_0X)_x$, then $v = p\,w$ for some $w \in N_1(x)$; and for all $x$ and $v \in N_1(x)$, if $u_1(x)(1\otimes v)$ lies in the image of the localisation of $\Pi_0$ plus $x\cdot(\mathrm{Lie}_1X)_x$, then $v \in N_0(x)$.
--
--   This is Drinfeld's nondegeneracy condition $[C_2]$ for the pair of lattice-to-tangent-germ maps attached to an admissible rigidified special formal $\mathcal{O}_D$-module over a base in which $p$ is nilpotent, in the form needed to exhibit the Cartier quadruple as a Deligne datum. It is used in the construction producing the tangent-germ stalk maps from the eta-section characterisation of the lattices $N_0 \le N_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_eq_smul_of_stalkMap_tmul_mem_sup_of_tangent_germ_wittVector
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
    (∀ (x : PrimeSpectrum B) (v : ↥(N₀ x)),
          u₀ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] v) ∈
            (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₁)).restrictScalars B ⊔
              x.asIdeal • (⊤ : Submodule B (FormalOmega.stalk B x ↥(t.X.lieZero (structureMap ι ψ)))) →
          ∃ w ∈ N₁ x, (v : Fin 2 → ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • w) ∧
      (∀ (x : PrimeSpectrum B) (v : ↥(N₁ x)),
          u₁ x ((1 : FormalOmega.locRing B x) ⊗ₜ[ℤ_[p]] v) ∈
            (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₀)).restrictScalars B ⊔
              x.asIdeal • (⊤ : Submodule B (FormalOmega.stalk B x ↥(t.X.lieOne (structureMap ι ψ)))) →
          (v : Fin 2 → ℚ_[p]) ∈ N₀ x) := by sorry
