-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_inclBaseChange_eq_map_of_tangent_germ
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.stalkMap_inclBaseChange_eq_map_of_tangent_germ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/39b4a7ab-2ad2-51fb-a660-e4c7565ebc81
-- title:
--   Pi-linearity of the tangent-germ stalk maps u₀,u₁
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring map $\iota\colon W(\mathbb F_{p^2})\to O$, and a formal $\mathcal O_D$-module $\Phi$ over $O/pO$ which is special for $\bar\jmath=\iota$ followed by reduction (its Lie algebra is the direct sum of the two eigenpieces `lieZero`, `lieOne`, both invertible) and of height $4$; assume the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary (`hcΦ`), let $r_\Phi\colon\mathbb Z_p^2\to N$ be an additive map into the $N$-module of the resulting graded Cartier datum, assume a canonical $L$-map for that datum exists, and assume $r_\Phi$ maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\eta(L)\cap N_0$ for every canonical $L$. Let $B$ be a Noetherian $\mathbb Z_p$-algebra with $p$ nilpotent, $\psi\colon O\to B$ a ring map, and $t=(X,n,\rho)$ a rigidified triple over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, of height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to $\bar X$. Let $N_0,N_1$ assign to each $x\in\operatorname{Spec}B$ a $\mathbb Z_p$-submodule of $\mathbb Q_p^2$, characterised by: $v\in N_i(x)$ iff there are $f\notin x$, complementarity data `IsGradedS`, `IsGradedSbar`, `IsGradedPhiS` over $B_f$, a canonical $L$ for the graded Cartier datum of $X$ over $B_f$, and an element $z$ with `IsEtaSection … i z v`, i.e. $z$ lies in the degree-$i$ $\eta$-piece and the lattice relation holds between the rigidified numerator over $\bar X_f$, the reduction of $\varpi^i z$, and $p^i v$. Assume each $N_i(x)$ is a full lattice (finitely generated, spanning $\mathbb Q_p^2$), $N_0(x)\le N_1(x)$, and $p\,N_1(x)\subseteq N_0(x)$. Let $\Pi_0\colon(\operatorname{Lie}X)_0\to(\operatorname{Lie}X)_1$ and $\Pi_1\colon(\operatorname{Lie}X)_1\to(\operatorname{Lie}X)_0$ be $B$-linear maps which on $\operatorname{Lie}X=B^2$ are both given by `lieVarpi`, the linear part of $\varpi$. Let $u_i(x)\colon B_x\otimes_{\mathbb Z_p}N_i(x)\to((\operatorname{Lie}X)_i)_x$ be $B_x$-linear, and assume the germ clauses `hg₀`, `hg₁`: for every $x$, every $v\in N_i(x)$ and every presentation $(f,L,z)$ of $v$ as above there are $m$ in the Cartier module over $B_f$, a section $s$ of $(\operatorname{Lie}X)_i$ and $b\notin x$ with $m$ mod the image of Verschiebung equal to the value of the datum's map `u` at $L$ and $z$, with $u_i(x)(1\otimes v)=s/b$ in the localised module, and with the image of each coordinate $s_j$ in $B_x$ equal to $b$ times the image of the $j$-th tangent coordinate of $m$ under $B_f\to B_x$. The conclusion is the pair of identities: for all $x$ and $w\in B_x\otimes N_0(x)$, $u_1(x)$ applied to the base change of the inclusion $N_0(x)\le N_1(x)$ of $w$ equals the localisation of $\Pi_0$ applied to $u_0(x)(w)$; and for all $x$ and $w\in B_x\otimes N_1(x)$, $u_0(x)$ applied to the base change of multiplication by $p$ (as a map $N_1(x)\to N_0(x)$) of $w$ equals the localisation of $\Pi_1$ applied to $u_1(x)(w)$.
--
--   This is the $\mathcal O_D$-linearity of the tangent-germ comparison maps in the Čerednik–Drinfeld uniformisation: the lattice maps $N_0(x)\hookrightarrow N_1(x)$ and $p\colon N_1(x)\to N_0(x)$ of the lattice-tree side correspond under $u$ to the two graded components of $\varpi$ acting on the Lie algebra of the special formal module, as in Boutot–Carayol II (3.13). It is used by the existence statement producing the stalk maps $u_0,u_1$ from the $\eta$-section description of $N_0,N_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_stalkMap_inclBaseChange_eq_map_of_tangent_germ.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.stalkMap_inclBaseChange_eq_map_of_tangent_germ
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
    (∀ x w, u₁ x (FormalOmega.inclBaseChange (FormalOmega.locRing B x) (M' := ⟨N₀ x, hfull₀ x⟩) (M := ⟨N₁ x, hfull₁ x⟩) (hle x) w) =
          LocalizedModule.map x.asIdeal.primeCompl Pi₀ (u₀ x w)) ∧
      (∀ x w, u₀ x (((FormalOmega.smulInto (p : ℤ_[p]) (hsmul x)).baseChange (FormalOmega.locRing B x) :
            FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
              FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩) w) =
          LocalizedModule.map x.asIdeal.primeCompl Pi₁ (u₁ x w)) := by sorry
