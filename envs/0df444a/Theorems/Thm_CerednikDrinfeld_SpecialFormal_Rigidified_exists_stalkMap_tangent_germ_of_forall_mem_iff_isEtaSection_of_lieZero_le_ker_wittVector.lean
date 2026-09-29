-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/13950a6f-8ea7-5bca-8a95-5c2bf57dab29
-- title:
--   Drinfeld stalk maps u₀,u₁ over W(k)
-- statement:
--   Throughout, $p$ is a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to \mathbb{W}(k)$ a ring homomorphism, where `Zp2 p` denotes the Witt vectors of the field `GaloisField p 2`. Let $\Phi$ be a formal $\mathcal O_D$-module over $\mathbb{W}(k)/p\,\mathbb{W}(k)$, i.e. an object of `FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k))`: a two-dimensional commutative formal group law together with an action of `Zp2 p` by formal-group endomorphisms and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$. Write $\bar\jmath =$ `Rigidified.jbar ι` for $\iota$ followed by reduction modulo $p$.
--
--   Hypotheses on $\Phi$. `hΦ` asserts that $\Phi$ is special for $\bar\jmath$: the submodules $\mathrm{Lie}_0 = \bigcap_a \ker(\mathrm{lieAct}\,a - \bar\jmath(a))$ and $\mathrm{Lie}_1 = \bigcap_a \ker(\mathrm{lieAct}\,a - \bar\jmath(\sigma a))$ of $\mathrm{Lie}\,\Phi = (\mathbb{W}(k)/p)^2$ are complementary and each invertible. `hΦ4` asserts that $\Phi$ has height $4$, i.e. the series of the action of $p$ has kernel of degree $p^4$. `h0Φ` asserts $\mathrm{Lie}_0 \subseteq \ker(\Phi.\mathrm{lieVarpi})$, the kernel of multiplication by the linear part of $\varpi$ (the degree-zero index is critical for $\Phi$). `hcΦ` asserts that the graded pieces of degree $0$ and $1$ of the Cartier module of $\Phi$ — the subgroups of those $f$ with $\mathrm{endAct}([c])f = \bar\jmath([c])^{p^n} f$ for all Teichmüller lifts $[c]$, $c \in \mathbb{F}_{p^2}$ — are complementary; this makes `Φ.toGradedCartierModuleData (jbar ι) hcΦ` a graded Cartier module datum $D_\Phi$, with underlying module the Cartier module of $\Phi$, Frobenius, Verschiebung, the operator induced by $\varpi$, and the two graded pieces. Further, $r_\Phi$ is an additive map $\mathbb{Z}_p^2 \to D_\Phi.\mathrm{NMod} = (M \times M^\sigma)/\mathrm{nRel}$; `hLΦ` asserts that a canonical $L$-map for $D_\Phi$ exists (a Cartier $L$-map admitting a presentation as the base change, along a surjection from a $p$-torsion-free ring, of an $L$-map on a special graded Cartier module); and `hrΦ` asserts that for every canonical $L$-map $L$ the map $r_\Phi$ carries $\mathbb{Z}_p^2$ bijectively onto the $\eta$-piece `etaPiece L _ 0`, the intersection of the $\eta$-subgroup of $L$ with the degree-zero piece of $D_\Phi.\mathrm{NMod}$.
--
--   Base and rigidified module. $B$ is a noetherian commutative $\mathbb{Z}_p$-algebra, $\psi : \mathbb{W}(k) \to B$ a ring homomorphism, and `hB` asserts that $p$ is nilpotent in $B$. The object $t :$ `Rigidified p Φ B` consists of a formal $\mathcal O_D$-module $X = t.X$ over $B$, a natural number $n = t.n$, and a series $\rho = t.\rho$ over $B/pB$. The hypothesis `ht` asserts admissibility: $X$ is special for the structure map $\psi \circ \iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from the base change $\bar\Phi_\psi$ to $\bar X$; its third component is the homomorphism datum used below in the $\eta$-section condition.
--
--   Lattice data. $N_0, N_1$ assign to each $x \in \operatorname{Spec} B$ a $\mathbb{Z}_p$-submodule of $\mathbb{Q}_p^2$. The hypotheses `hN₀` and `hN₁` characterise them: for $i = 0,1$, a vector $v$ lies in $N_i(x)$ if and only if there are $f \in B \setminus x$, complementarity hypotheses `hc`, `hcb`, `hcΦf` for the degree-$0$ and degree-$1$ graded pieces of the Cartier modules of $X$ over the localisation $B_f$, of $\bar X$ over $B_f/p$ and of $\bar\Phi_\psi$ over $B_f/p$ respectively, a canonical $L$-map $L$ for the graded Cartier datum $D_f$ of $X$ over $B_f$, and an element $z$ of $D_f.\mathrm{NMod}$ with `t.IsEtaSection … i z v`; the latter says that $z$ lies in `etaPiece L _ i` and that the relation `LatticeRel` holds for the graded datum of $\bar X$ over $B_f/p$, with integer $t.n$, with the map `rigidNum` obtained from $r_\Phi$ by base change along $\psi$ and $f$ followed by the map induced by $\rho$, with the element obtained by applying the reduction `etaRed` to the $i$-th power of the $\varpi$-operator applied to $z$, and with the vector $p^i v$; concretely, $\mathrm{LatticeRel}\,E\,n\,r\,\bar z\,v$ means that there are $m, k \in \mathbb{N}$ and $w \in \mathbb{Z}_p^2$ with $p^m v = w$ in $\mathbb{Q}_p^2$ and $p^k\, r(w) = p^{k+n+m}\,\bar z$.
--
--   The hypotheses `hfull₀`, `hfull₁` assert that each $N_i(x)$ is a full lattice: finitely generated over $\mathbb{Z}_p$ and spanning $\mathbb{Q}_p^2$ over $\mathbb{Q}_p$. The hypotheses `hle` and `hsmul` assert $N_0(x) \subseteq N_1(x)$ and $p\,N_1(x) \subseteq N_0(x)$ for every $x$.
--
--   Graded $\varpi$ on $\mathrm{Lie}\,X$. Finally $\Pi_0$ is a $B$-linear map from $\mathrm{Lie}_0(X)$ to $\mathrm{Lie}_1(X)$ and $\Pi_1$ a $B$-linear map from $\mathrm{Lie}_1(X)$ to $\mathrm{Lie}_0(X)$ (eigen-submodules of $\mathrm{Lie}\,X = B^2$ for the structure map $\psi\circ\iota$), and the hypotheses `hPi₀`, `hPi₁` assert that on underlying vectors both are given by `t.X.lieVarpi`, multiplication by the linear part of $\varpi$ on $X$.
--
--   Conclusion. There exist families, indexed by the primes $x$ of $B$, of $B_x$-linear maps
--   $$u_0(x) : B_x \otimes_{\mathbb{Z}_p} N_0(x) \to (\mathrm{Lie}_0(X))_x, \qquad u_1(x) : B_x \otimes_{\mathbb{Z}_p} N_1(x) \to (\mathrm{Lie}_1(X))_x,$$
--   where $B_x =$ `Localization.AtPrime x.asIdeal` and the targets are the localisations `LocalizedModule x.asIdeal.primeCompl` of $\mathrm{Lie}_0(X)$, $\mathrm{Lie}_1(X)$, such that the following ten assertions hold.
--
--   (1) For $i = 0$: for every prime $x$, every $v \in N_0(x)$ and every presentation of $v$ as in `hN₀` — data $f \notin x$, `hc`, `hcb`, `hcΦf`, a canonical $L$-map $L$ for $D_f$, and $z$ with `t.IsEtaSection … 0 z v` — there are an element $m$ of the Cartier module $D_f.M$, a section $s \in \mathrm{Lie}_0(X)$ and $b \notin x$ such that the class of $m$ modulo $D_f.\mathrm{vRange}$ (the image of Verschiebung) equals the value at $z$, viewed in the $\eta$-subgroup of $L$, of the map `u` of $D_f$ attached to $L$; such that $u_0(x)(1 \otimes v) = s/b$ in $(\mathrm{Lie}_0(X))_x$; and such that for each coordinate $i$ the image of $s_i$ in $B_x$ equals the image of $b$ times the image, under the canonical map $B_f \to B_x$, of the $i$-th coordinate of the tangent vector [`MvFormalGroup.CartierModule.tangent m`](def/MvFormalGroup_CartierModule.html#L1037).
--
--   (2) The same assertion with $0$ replaced by $1$ throughout, for $N_1$, $u_1$ and $\mathrm{Lie}_1(X)$.
--
--   (3) For every $x$ and every $w \in B_x \otimes_{\mathbb{Z}_p} N_0(x)$, the image of $w$ under the base change of the inclusion $N_0(x) \subseteq N_1(x)$, followed by $u_1(x)$, equals the localisation of $\Pi_0$ applied to $u_0(x)(w)$.
--
--   (4) For every $x$ and every $w \in B_x \otimes_{\mathbb{Z}_p} N_1(x)$, the image of $w$ under the base change of multiplication by $p$, $N_1(x) \to N_0(x)$, followed by $u_0(x)$, equals the localisation of $\Pi_1$ applied to $u_1(x)(w)$.
--
--   (5), (6) Each $u_0(x)$ and each $u_1(x)$ is surjective.
--
--   (7) For every prime $x$ and every $v \in N_0(x)$ there are $f \notin x$ and $s \in \mathrm{Lie}_0(X)$ such that for every prime $y$ with $f \notin y$ one has $v \in N_0(y)$ and $u_0(y)(1 \otimes v) = s/f$ in $(\mathrm{Lie}_0(X))_y$.
--
--   (8) The same with $N_1$, $u_1$ and $\mathrm{Lie}_1(X)$.
--
--   (9) For every prime $x$ and every $v \in N_0(x)$: if $u_0(x)(1 \otimes v)$ lies in the sum of the range of the localisation of $\Pi_1$ (as a $B$-submodule) and of $x \cdot (\mathrm{Lie}_0(X))_x$, then there is $w \in N_1(x)$ with $v = p\,w$.
--
--   (10) For every prime $x$ and every $v \in N_1(x)$: if $u_1(x)(1 \otimes v)$ lies in the sum of the range of the localisation of $\Pi_0$ (as a $B$-submodule) and of $x \cdot (\mathrm{Lie}_1(X))_x$, then $v \in N_0(x)$.
--
--   This is the step of the Čerednik–Drinfeld uniformisation that produces, from an admissible rigidified special formal $\mathcal O_D$-module over a noetherian $\mathbb{Z}_p$-algebra with $p$ nilpotent and from the associated $\eta$-lattices $N_0 \subseteq N_1$, the stalkwise period maps $u_0, u_1$ with their compatibility with the graded pieces of $\varpi$ on the Lie algebra, their surjectivity, their local constancy along sections, and the injectivity conditions modulo $\varpi$ and the prime; these are exactly the fields of the Drinfeld datum attached to the rigidified module. It is the base-$\mathbb{W}(k)$ form of the general statement `exists_stalkMap_tangent_germ`, and is cited by [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_isCartierQuadruple_of_isAdmissible_of_lieVarpi_eq_zero_wittVector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_stalkMap_tangent_germ_of_forall_mem_iff_isEtaSection_of_lieZero_le_ker_wittVector
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
            Rigidified.locHom x (b : B) * Rigidified.awayToLoc x f hf (MvFormalGroup.CartierModule.tangent m i)) ∧

      (∀ x w, u₁ x (FormalOmega.inclBaseChange (FormalOmega.locRing B x) (M' := ⟨N₀ x, hfull₀ x⟩) (M := ⟨N₁ x, hfull₁ x⟩) (hle x) w) =
          LocalizedModule.map x.asIdeal.primeCompl Pi₀ (u₀ x w)) ∧
      (∀ x w, u₀ x (((FormalOmega.smulInto (p : ℤ_[p]) (hsmul x)).baseChange (FormalOmega.locRing B x) :
            FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₁ x, hfull₁ x⟩ →ₗ[FormalOmega.locRing B x]
              FormalOmega.latticeBaseChange ℤ_[p] ℚ_[p] (FormalOmega.locRing B x) ⟨N₀ x, hfull₀ x⟩) w) =
          LocalizedModule.map x.asIdeal.primeCompl Pi₁ (u₁ x w)) ∧

      (∀ x, Function.Surjective (u₀ x)) ∧ (∀ x, Function.Surjective (u₁ x)) ∧

      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x →
          ∃ (f : B) (s : ↥(t.X.lieZero (structureMap ι ψ))), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
            ∃ hv : v ∈ N₀ y, u₀ y ((1 : FormalOmega.locRing B y) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₀ y))) = LocalizedModule.mk s ⟨f, hy⟩) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x →
          ∃ (f : B) (s : ↥(t.X.lieOne (structureMap ι ψ))), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
            ∃ hv : v ∈ N₁ y, u₁ y ((1 : FormalOmega.locRing B y) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(N₁ y))) = LocalizedModule.mk s ⟨f, hy⟩) ∧

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
