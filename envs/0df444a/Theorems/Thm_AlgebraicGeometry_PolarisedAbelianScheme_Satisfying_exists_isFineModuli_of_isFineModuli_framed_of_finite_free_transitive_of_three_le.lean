-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/126cd101-5a70-5596-894f-23cfdb2d5f89
-- title:
--   Finite free quotient of a framed fine moduli scheme
-- statement:
--   Fixed throughout are natural numbers $g, N, n$ with $3 \le n$, a commutative ring $\mathcal O$ in which $n$ is a unit, and a property $Q$ assigning to every commutative ring $S$ a predicate on `PolarisedAbelianScheme g (N + 1) n S`, that is, on abelian schemes $A \to \operatorname{Spec} S$ of relative dimension $g$ with commutative relative group law, a full level-$n$ structure given by $2g$ sections $P_i$ generating the $n$-torsion of every geometric fibre, and an invertible module `pol` which is very ample for $f$ and has $d = N+1$ as the $H^0$-rank on every geometric fibre.
--
--   The hypotheses on $Q$ and on polarised abelian schemes are: `hQbc`, stability of $Q$ under base change (if `PolarisedAbelianScheme.IsPullback φ u u'` for a ring map $φ : S \to S'$ and $Q\,S\,u$ holds, then $Q\,S'\,u'$ holds); `hQdesc`, descent of $Q$ along faithfully flat étale algebras $S \to S'$; `hSHEAF`, Zariski gluing for polarised abelian schemes in the general form (for all $g, d, n$ with $3 \le n$, any ring $S$ in which $n$ is a unit, any $r : \mathrm{Fin}\,k \to S$ with $\operatorname{span}(\operatorname{range} r) = \top$ and any localisations $B_i$ of $S$ away from $r_i$: first, a family $u_i$ over $B_i$ whose pullbacks along any two $S$-algebra maps $B_i \to C$, $B_j \to C$ into a localisation away from $r_i r_j$ are isomorphic admits $u_0$ over $S$ all of whose pullbacks to $B_i$ are isomorphic to $u_i$; second, two objects over $S$ with isomorphic pullbacks to every $B_i$ are isomorphic); `hEFF`, effectivity and faithfulness of descent along a faithfully flat $S$-algebra $S'$ (an object $u'$ over $S'$ whose two pullbacks to $S' \otimes_S S'$ along `includeLeft` and `includeRight` are isomorphic descends to some $u$ over $S$, and objects over $S$ with isomorphic pullbacks to $S'$ are isomorphic); and `hBC`, existence of a base change $u'$ over $S'$ of any $u$ over $S$ along any ring map.
--
--   Next, $Θ$ assigns to every commutative ring $S$ a predicate on `FramedPolarisedAbelianScheme g N n S`, i.e. on polarised abelian schemes of degree $N+1$ and level $n$ equipped with a frame: a `Scheme.Modules.ProjPresentation` of `pol` over $f$ with $N+1$ sections $σ_i$ and a structural map to $\operatorname{Proj}$ of the polynomial ring in $N+1$ variables over $S$, this map being a closed immersion and the $σ_i$ forming a section basis on the whole of $A$. The hypotheses on $Θ$ are: `hΘQ`, that $Θ\,S\,X$ implies $Q\,S$ of the underlying polarised abelian scheme (stated for every morphism $\operatorname{Spec} S \to \operatorname{Spec}\mathcal O$); `hΘiso`, invariance of $Θ$ under `FramedPolarisedAbelianScheme.Iso`; `hΘbc`, stability of $Θ$ under base change along any ring map (again quantified over a morphism $\operatorname{Spec} S \to \operatorname{Spec}\mathcal O$); and `hΘBC`, existence of base changes of framed objects along any ring map.
--
--   The framed moduli data consist of a scheme $H_Θ$ (in universe $0$), a morphism $π_Θ : H_Θ \to \operatorname{Spec}\mathcal O$, and a map $\mathrm{pt}_Θ$ sending each ring $S$, each morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and each framed $X$ with $Θ\,S\,X$ to an element of `SchemeHomOver s πΘ`, that is, a morphism $\operatorname{Spec} S \to H_Θ$ whose composite with $π_Θ$ is $s$. Four hypotheses make this a fine moduli scheme for $Θ$-framed objects: `hpt_iso` (constancy on `FramedPolarisedAbelianScheme.Iso`-classes), `hpt_pullback` (for $φ : S \to S'$ with $\operatorname{Spec}(φ)$ followed by $s$ equal to $s'$, and $X'$ a base change of $X$, the underlying morphism of $\mathrm{pt}_Θ\,S'\,s'\,X'$ is $\operatorname{Spec}(φ)$ followed by that of $\mathrm{pt}_Θ\,S\,s\,X$), `hpt_surjective` (every element of `SchemeHomOver s πΘ` is $\mathrm{pt}_Θ\,S\,s\,X$ for some $Θ$-framed $X$) and `hpt_injective` (equality of two such points forces an isomorphism of the framed objects). Further, $π_Θ$ is separated (`hsep`), quasi-compact (`hqc`) and locally of finite presentation (`hfp`), and `hAF` requires every finite subset of $H_Θ$ to be contained in an affine open.
--
--   Finally, $Γ$ is a finite group with a homomorphism $ρ : Γ \to \operatorname{Aut} H_Θ$ whose automorphisms are morphisms over $\operatorname{Spec}\mathcal O$ ($ρ(γ)$ followed by $π_Θ$ equals $π_Θ$, hypothesis `hρ`), together with an operation `act` giving, for each ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and each $γ \in Γ$, a transformation of framed objects over $S$ subject to: `hactΘ`, preservation of $Θ$; `hact_val`, that the underlying polarised abelian scheme is unchanged, so that only the frame is moved; `hact_pt`, that the underlying morphism of $\mathrm{pt}_Θ\,S\,s\,(\mathrm{act}\,S\,s\,γ\,X)$ is that of $\mathrm{pt}_Θ\,S\,s\,X$ followed by $ρ(γ)$; `hfree`, that over a nontrivial ring $S$ an isomorphism $\mathrm{act}\,S\,s\,γ\,X \cong X$ with $Θ\,S\,X$ forces $γ = 1$; and `htrans`, local transitivity of the action on frames: if $Θ\,S\,X$ and $Θ\,S\,X'$ hold and the underlying polarised abelian schemes are isomorphic, there are $m$ and $r : \mathrm{Fin}\,m \to S$ with $\operatorname{span}(\operatorname{range} r) = \top$ such that for every $j$ and all base changes $Y, Y'$ of $X, X'$ to `Localization.Away (r j)` there is $γ \in Γ$ with $\mathrm{act}\,γ\,Y \cong Y'$ over that localisation. The last hypothesis, `hsurj`, asserts that every $u$ over $S$ with $Q\,S\,u$ becomes framed after a faithfully flat extension: there are a faithfully flat $S$-algebra $S'$ and a framed $X'$ over $S'$ with $Θ\,S'\,X'$ whose underlying polarised abelian scheme is a base change of $u$ along $S \to S'$.
--
--   Under these hypotheses there exist a scheme $M$ in universe $0$, a morphism $π_M : M \to \operatorname{Spec}\mathcal O$, a map $\mathrm{pt}$ sending each ring $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and each element of `PolarisedAbelianScheme.Satisfying g (N + 1) n Q S` (a polarised abelian scheme over $S$ of degree $N+1$ and level $n$ together with a proof of $Q$) to an element of `SchemeHomOver s πM`, and a morphism $q : H_Θ \to M$ with $ρ(γ)$ followed by $q$ equal to $q$ for every $γ \in Γ$, such that the following hold.
--
--   First, $(M, π_M, \mathrm{pt})$ satisfies `PolarisedAbelianScheme.Satisfying.IsFineModuli g (N + 1) n Q M πM pt`: $\mathrm{pt}$ is constant on isomorphism classes (where two $Q$-objects are isomorphic when their underlying polarised abelian schemes are), compatible with base change in the sense above, surjective onto `SchemeHomOver s πM` for every $(S, s)$, and injective up to isomorphism; moreover $π_M$ is separated, quasi-compact and locally of finite presentation, and every finite subset of $M$ is contained in an affine open.
--
--   Second, $q$ exhibits $M$ as the quotient of $H_Θ$ by $Γ$: $q$ followed by $π_M$ equals $π_Θ$; $q$ is finite and flat; the map $q$ induces a surjection on underlying points; two points of $H_Θ$ have the same image under $q$ precisely when they lie in a common $Γ$-orbit, i.e. $q_{\mathrm{base}}(x) = q_{\mathrm{base}}(x')$ if and only if $(ρ\,γ)_{\mathrm{base}}(x) = x'$ for some $γ$; for every open $V \subseteq M$ the map on sections $q.\mathrm{app}\,V$ is injective, and its range is exactly the set of sections $t$ over $q^{-1}V$ fixed by every $γ \in Γ$ (the action being by $(ρ\,γ).\mathrm{appLE}$ on $q^{-1}V$, which is $Γ$-stable since $ρ(γ)$ followed by $q$ is $q$); and every affine open $U \subseteq H_Θ$ with $(ρ\,γ)^{-1}U = U$ for all $γ$ is of the form $q^{-1}V$ for some affine open $V \subseteq M$.
--
--   This is the descent step which passes from a fine moduli scheme for rigidified (framed) polarised abelian schemes to one for the unframed moduli problem cut out by $Q$: the frame is removed by forming the quotient of $H_Θ$ by the finite group $Γ$ that acts freely on frames and transitively on them locally on the base, the quotient inheriting separatedness, quasi-compactness, local finite presentation and the property that finite sets of points lie in affine opens. It feeds the construction of the moduli scheme used for the modular-curve-type moduli problems, being cited by [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_thetaCore`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_thetaTypeLocally_of_isFineModuli_framed_thetaCore).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le
    (g N n : ℕ) (hn : 3 ≤ n) (𝒪 : Type) [CommRing 𝒪] (hn' : IsUnit ((n : ℕ) : 𝒪))
    (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g (N + 1) n S → Prop)

    (hQbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S'),
      PolarisedAbelianScheme.IsPullback φ u u' → Q S u → Q S' u')
    (hQdesc : ∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S'] [Algebra.Etale S S']
      (u : PolarisedAbelianScheme g (N + 1) n S) (u' : PolarisedAbelianScheme g (N + 1) n S'),
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u u' → Q S' u' → Q S u)
    (hSHEAF : ∀ {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
      {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
      (B : Fin k → Type) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)],
      (∀ (u : ∀ i, PolarisedAbelianScheme g d n (B i)),
      (∀ (i j : Fin k) (C : Type) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
      (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C) (v₁ v₂ : PolarisedAbelianScheme g d n C),
      PolarisedAbelianScheme.IsPullback ρ₁.toRingHom (u i) v₁ →
      PolarisedAbelianScheme.IsPullback ρ₂.toRingHom (u j) v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂) →
      ∃ u₀ : PolarisedAbelianScheme g d n S, ∀ (i : Fin k) (v : PolarisedAbelianScheme g d n (B i)),
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v → PolarisedAbelianScheme.Iso v (u i)) ∧
      (∀ (u₀ u₀' : PolarisedAbelianScheme g d n S),
      (∀ (i : Fin k) (v v' : PolarisedAbelianScheme g d n (B i)),
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀ v →
      PolarisedAbelianScheme.IsPullback (algebraMap S (B i)) u₀' v' →
      PolarisedAbelianScheme.Iso v v') →
      PolarisedAbelianScheme.Iso u₀ u₀'))
    (hEFF : ∀ {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
      (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
      (u' : PolarisedAbelianScheme g d n S')
      (hdesc : ∀ (v₁ v₂ : PolarisedAbelianScheme g d n (S' ⊗[S] S')),
      PolarisedAbelianScheme.IsPullback
      (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₁ →
      PolarisedAbelianScheme.IsPullback
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂),
      (∃ u : PolarisedAbelianScheme g d n S, ∀ v : PolarisedAbelianScheme g d n S',
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u v → PolarisedAbelianScheme.Iso v u') ∧
      (∀ (u₁ u₂ : PolarisedAbelianScheme g d n S) (v₁ v₂ : PolarisedAbelianScheme g d n S'),
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u₁ v₁ →
      PolarisedAbelianScheme.IsPullback (algebraMap S S') u₂ v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂ → PolarisedAbelianScheme.Iso u₁ u₂))
    (hBC : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (u : PolarisedAbelianScheme g (N + 1) n S),
      ∃ u' : PolarisedAbelianScheme g (N + 1) n S', PolarisedAbelianScheme.IsPullback φ u u')
    (Θ : ∀ (S : Type) [CommRing S], FramedPolarisedAbelianScheme g N n S → Prop)
    (hΘQ : ∀ (S : Type) [CommRing S] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → Q S X.toPolarisedAbelianScheme)
    (hΘiso : ∀ (S : Type) [CommRing S] (X X' : FramedPolarisedAbelianScheme g N n S),
      FramedPolarisedAbelianScheme.Iso X X' → Θ S X → Θ S X')
    (hΘbc : ∀ (S S' : Type) [CommRing S] [CommRing S'] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (φ : S →+* S')
      (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S'),
      FramedPolarisedAbelianScheme.IsPullback φ X X' → Θ S X → Θ S' X')
    (hΘBC : ∀ {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (X : FramedPolarisedAbelianScheme g N n S),
      ∃ X' : FramedPolarisedAbelianScheme g N n S', FramedPolarisedAbelianScheme.IsPullback φ X X')
    (HΘ : Scheme.{0}) (πΘ : HΘ ⟶ Spec (CommRingCat.of 𝒪))
    (ptΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → SchemeHomOver s πΘ)
    (hpt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'),
      FramedPolarisedAbelianScheme.Iso X X' → ptΘ S s X hX = ptΘ S s X' hX')
    (hpt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
      ∀ (X : FramedPolarisedAbelianScheme g N n S) (X' : FramedPolarisedAbelianScheme g N n S') (hX : Θ S X) (hX' : Θ S' X'),
      FramedPolarisedAbelianScheme.IsPullback φ X X' →
      (ptΘ S' s' X' hX').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptΘ S s X hX).1)
    (hpt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (x : SchemeHomOver s πΘ),
      ∃ (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X), ptΘ S s X hX = x)
    (hpt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X X' : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X) (hX' : Θ S X'), ptΘ S s X hX = ptΘ S s X' hX' →
      FramedPolarisedAbelianScheme.Iso X X')
    (hsep : IsSeparated πΘ) (hqc : QuasiCompact πΘ) (hfp : LocallyOfFinitePresentation πΘ)
    (hAF : ∀ F : Finset HΘ, ∃ U : HΘ.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut HΘ) (hρ : ∀ γ : Γ, (ρ γ).hom ≫ πΘ = πΘ)
    (act : ∀ (S : Type) [CommRing S], (Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) →
      Γ → FramedPolarisedAbelianScheme g N n S → FramedPolarisedAbelianScheme g N n S)
    (hactΘ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S), Θ S X → Θ S (act S s γ X))
    (hact_val : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S),
      (act S s γ X).toPolarisedAbelianScheme = X.toPolarisedAbelianScheme)
    (hact_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (γ : Γ) (X : FramedPolarisedAbelianScheme g N n S) (hX : Θ S X),
      (ptΘ S s (act S s γ X) (hactΘ S s γ X hX)).1 = (ptΘ S s X hX).1 ≫ (ρ γ).hom)

    (hfree : ∀ (S : Type) [CommRing S] [Nontrivial S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (γ : Γ)
      (X : FramedPolarisedAbelianScheme g N n S), Θ S X → FramedPolarisedAbelianScheme.Iso (act S s γ X) X → γ = 1)

    (htrans : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X X' : FramedPolarisedAbelianScheme g N n S), Θ S X → Θ S X' →
      PolarisedAbelianScheme.Iso X.toPolarisedAbelianScheme X'.toPolarisedAbelianScheme →
      ∃ (m : ℕ) (r : Fin m → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ (j : Fin m)
        (Y Y' : FramedPolarisedAbelianScheme g N n (Localization.Away (r j))),
        FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X Y →
        FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X' Y' →
        ∃ γ : Γ, FramedPolarisedAbelianScheme.Iso
          (act (Localization.Away (r j)) (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (r j)))) ≫ s) γ Y) Y')

    (hsurj : ∀ (S : Type) [CommRing S] (_s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : PolarisedAbelianScheme g (N + 1) n S), Q S u →
      ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S'), Module.FaithfullyFlat S S' ∧
        ∃ X' : FramedPolarisedAbelianScheme g N n S', Θ S' X' ∧
          PolarisedAbelianScheme.IsPullback (algebraMap S S') u X'.toPolarisedAbelianScheme) :
    ∃ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪))
      (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        PolarisedAbelianScheme.Satisfying g (N + 1) n Q S → SchemeHomOver s πM)
      (q : HΘ ⟶ M) (hq : ∀ γ : Γ, (ρ γ).hom ≫ q = q),
      (PolarisedAbelianScheme.Satisfying.IsFineModuli g (N + 1) n Q M πM pt ∧
        IsSeparated πM ∧ QuasiCompact πM ∧ LocallyOfFinitePresentation πM ∧
        (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)) ∧

      (q ≫ πM = πΘ ∧ IsFinite q ∧ Flat q ∧ Function.Surjective q.base ∧
        (∀ x x' : HΘ, q.base x = q.base x' ↔ ∃ γ : Γ, (ρ γ).hom.base x = x') ∧
        (∀ V : M.Opens, Function.Injective (q.app V)) ∧
        (∀ V : M.Opens, Set.range (q.app V) =
          {t | ∀ γ : Γ, (ρ γ).hom.appLE (q ⁻¹ᵁ V) (q ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hq γ]) t = t}) ∧
        (∀ U : HΘ.Opens, IsAffineOpen U → (∀ γ : Γ, (ρ γ).hom ⁻¹ᵁ U = U) → ∃ V : M.Opens, IsAffineOpen V ∧ q ⁻¹ᵁ V = U)) := by sorry
