-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_pt_comp_eq_of_finite_free_transitive
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_pt_comp_eq_of_finite_free_transitive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/086710e8-b74d-5f1c-a720-a42b10e1cb6a
-- title:
--   Classifying map to the quotient M by flat descent of frames
-- statement:
--   Throughout, a *polarised abelian scheme of type* $(g,d,n)$ over a commutative ring $S$ (`PolarisedAbelianScheme g d n S`) consists of a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$ on $f$, the bundle of properties of an abelian scheme, fibres of topological Krull dimension $g$, a family of $2g$ sections $P_i$ of $f$ over $\operatorname{Spec} S$ that are killed by $n$ and that on every geometric fibre are independent and generate the $n$-torsion, together with an invertible module `pol` on $A$ admitting a closed immersion by its sections and having geometric fibrewise space of sections of dimension $d$. A *framed* polarised abelian scheme of type $(g,N,n)$ (`FramedPolarisedAbelianScheme g N n S`) is such an object of type $(g,N+1,n)$ equipped with a `ProjPresentation` of `pol` relative to $f$ with $N+1$ sections, that is, $N+1$ global sections of `pol` and a morphism $A \to \mathbb{P}^N_S$ over $\operatorname{Spec} S$ trivialising `pol` on the standard charts, required to be a closed immersion and to be a section basis for `pol`. For both structures `Iso` means an isomorphism of the underlying schemes over the base compatible with the group law, with the marked sections $P_i$, and locally on the base with the polarisation module (in the framed case also with the morphism to projective space), while `IsPullback φ X X'` asserts the existence of a morphism $X'.A \to X.A$ forming a pullback square with $X'.f$, $X.f$ and $\operatorname{Spec}(\varphi)$, compatible with the group laws, the sections, and the polarisation modules (in the framed case also: $X'.\mathrm{frame}.\mathrm{toProj}$ followed by `ProjSpace.map` equals that morphism followed by $X.\mathrm{frame}.\mathrm{toProj}$). An element of `SchemeHomOver s πΘ` is a morphism $\operatorname{Spec} S \to H_\Theta$ whose composite with $\pi_\Theta$ is $s$.
--
--   Fix natural numbers $g, N, n$ with $3 \le n$ and a commutative ring $\mathcal{O}$ in which the image of $n$ is a unit. The data are: a predicate $Q$ on polarised abelian schemes of type $(g,N+1,n)$ over arbitrary commutative rings; a predicate $\Theta$ on framed polarised abelian schemes of type $(g,N,n)$; a scheme $H_\Theta$ with a morphism $\pi_\Theta : H_\Theta \to \operatorname{Spec}\mathcal{O}$; an assignment $\mathrm{pt}_\Theta$ which to every ring $S$, every morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and every framed object $X$ over $S$ with $\Theta\,S\,X$ associates a point of $H_\Theta$ over $s$; a finite group $\Gamma$ with a homomorphism $\rho : \Gamma \to \operatorname{Aut} H_\Theta$ and an action `act` of $\Gamma$ on framed objects over each pair $(S,s)$; and finally a scheme $M$ with $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ and a morphism $q : H_\Theta \to M$.
--
--   The hypotheses fall into the following groups. On $Q$: `hQbc` says $Q$ is stable under base change along arbitrary ring homomorphisms, and `hQdesc` says $Q$ descends along a faithfully flat étale algebra map $S \to S'$ (if $u'$ over $S'$ is the base change of $u$ and $Q\,S'\,u'$ holds, then $Q\,S\,u$). General descent and gluing for polarised abelian schemes (all stated for arbitrary $g, d, n$ with $3 \le n$ and $n$ invertible in the base ring, and summarised here): `hSHEAF` is Zariski gluing along a finite family $r : \mathrm{Fin}\,k \to S$ spanning the unit ideal with localisations $B_i$ away from $r_i$ — a family of objects over the $B_i$ whose pullbacks to any localisation away from $r_ir_j$ agree up to isomorphism is, up to isomorphism, the base change of an object over $S$, and an object over $S$ is determined up to isomorphism by its base changes to the $B_i$; `hEFF` is effectivity and uniqueness of descent along a faithfully flat algebra $S \to S'$, for an object over $S'$ whose two pullbacks to $S' \otimes_S S'$ are isomorphic; `hBC` asserts that base changes of objects of type $(g,N+1,n)$ exist along every ring homomorphism. On $\Theta$: `hΘQ` says that $\Theta\,S\,X$ implies $Q$ holds of the underlying polarised abelian scheme of $X$; `hΘiso` says $\Theta$ is invariant under `FramedPolarisedAbelianScheme.Iso`; `hΘbc` says $\Theta$ is stable under base change of framed objects; `hΘBC` says base changes of framed objects exist along every ring homomorphism. On $\mathrm{pt}_\Theta$: `hpt_iso` says it is constant on isomorphism classes of framed objects over a fixed $(S,s)$; `hpt_pullback` says that if $\operatorname{Spec}(\varphi)$ followed by $s$ is $s'$ and $X'$ over $S'$ is a base change of $X$ along $\varphi$, then the point of $X'$ is $\operatorname{Spec}(\varphi)$ followed by the point of $X$; `hpt_surjective` says every point of $H_\Theta$ over $s$ is the point of some $\Theta$-object; `hpt_injective` says two $\Theta$-objects over $(S,s)$ with the same point are isomorphic. On $\pi_\Theta$: it is separated (`hsep`), quasi-compact (`hqc`) and locally of finite presentation (`hfp`), and `hAF` requires every finite subset of $H_\Theta$ to lie in an affine open. On the $\Gamma$-action: `hρ` says each $\rho(\gamma)$ commutes with $\pi_\Theta$; `hactΘ` says `act` preserves $\Theta$; `hact_val` says `act` leaves the underlying polarised abelian scheme unchanged; `hact_pt` says the point of $\mathrm{act}\,\gamma\,X$ is the point of $X$ followed by $\rho(\gamma)$; `hfree` says that over a nontrivial $S$ an isomorphism $\mathrm{act}\,\gamma\,X \cong X$ with $\Theta\,S\,X$ forces $\gamma = 1$; `htrans` is local transitivity: if $X, X'$ satisfy $\Theta$ over $S$ and have isomorphic underlying polarised abelian schemes, then there is a finite family $r : \mathrm{Fin}\,m \to S$ spanning the unit ideal such that over each $\mathrm{Localization.Away}\,(r_j)$ any base changes $Y$ of $X$ and $Y'$ of $X'$ satisfy $\mathrm{act}\,\gamma\,Y \cong Y'$ for some $\gamma \in \Gamma$. Finally `hsurj` says every $u$ over $S$ with $Q\,S\,u$ admits a faithfully flat $S$-algebra $S'$ and a framed object $X'$ over $S'$ with $\Theta\,S'\,X'$ whose underlying polarised abelian scheme is the base change of $u$ along $S \to S'$; and on $q$: `hq` says $q$ is $\Gamma$-invariant, $\rho(\gamma)$ followed by $q$ being $q$ for all $\gamma$, `hqπ` says $q$ followed by $\pi_M$ is $\pi_\Theta$, and `horbit` says that for $\Theta$-objects $X_1, X_2$ over $(S,s)$ with isomorphic underlying polarised abelian schemes, the point of $X_1$ followed by $q$ equals the point of $X_2$ followed by $q$.
--
--   The conclusion asserts the existence of a rule $\mathrm{pt}$ which to every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and every $U$ in `PolarisedAbelianScheme.Satisfying g (N+1) n Q S` (a polarised abelian scheme $U.\mathrm{val}$ of type $(g,N+1,n)$ over $S$ together with a proof of $Q\,S\,U.\mathrm{val}$) assigns a morphism $\operatorname{Spec} S \to M$ whose composite with $\pi_M$ is $s$, subject to three conditions.
--
--   First, compatibility with frames: for all $\varphi : S \to S'$ and all $s, s'$ with $\operatorname{Spec}(\varphi)$ followed by $s$ equal to $s'$, for every $U$ over $S$ satisfying $Q$ and every framed object $X'$ over $S'$ with $\Theta\,S'\,X'$ such that $X'$'s underlying polarised abelian scheme is the base change of $U.\mathrm{val}$ along $\varphi$, the point $\mathrm{pt}_\Theta\,S'\,s'\,X'$ followed by $q$ equals $\operatorname{Spec}(\varphi)$ followed by $\mathrm{pt}\,S\,s\,U$.
--
--   Second, invariance under isomorphism: for $U, U'$ over $S$ satisfying $Q$ with `PolarisedAbelianScheme.Satisfying.Iso U U'`, that is with $U.\mathrm{val} \cong U'.\mathrm{val}$, one has $\mathrm{pt}\,S\,s\,U = \mathrm{pt}\,S\,s\,U'$.
--
--   Third, compatibility with base change: for all $\varphi : S \to S'$ and $s, s'$ with $\operatorname{Spec}(\varphi)$ followed by $s$ equal to $s'$, and all $U$ over $S$, $U'$ over $S'$ with `PolarisedAbelianScheme.Satisfying.IsPullback φ U U'`, that is with $U'.\mathrm{val}$ a base change of $U.\mathrm{val}$ along $\varphi$, the morphism $\mathrm{pt}\,S'\,s'\,U'$ equals $\operatorname{Spec}(\varphi)$ followed by $\mathrm{pt}\,S\,s\,U$.
--
--   This is the classifying-map step in the construction of a moduli scheme for polarised abelian schemes satisfying $Q$ as the quotient, by the free action of the finite group $\Gamma$ changing the frame, of a moduli scheme $H_\Theta$ for framed objects: a point of $M$ is attached to an object by framing it over a faithfully flat extension and descending the $\Gamma$-orbit of the framed point. It is used by [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_pt_comp_eq_of_finite_free_transitive.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_pt_comp_eq_of_finite_free_transitive
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
          PolarisedAbelianScheme.IsPullback (algebraMap S S') u X'.toPolarisedAbelianScheme)

    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (q : HΘ ⟶ M)
    (hq : ∀ γ : Γ, (ρ γ).hom ≫ q = q) (hqπ : q ≫ πM = πΘ)
    (horbit : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X₁ X₂ : FramedPolarisedAbelianScheme g N n S) (h₁ : Θ S X₁) (h₂ : Θ S X₂),
      PolarisedAbelianScheme.Iso X₁.toPolarisedAbelianScheme X₂.toPolarisedAbelianScheme →
      (ptΘ S s X₁ h₁).1 ≫ q = (ptΘ S s X₂ h₂).1 ≫ q) :
    ∃ (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
        PolarisedAbelianScheme.Satisfying g (N + 1) n Q S → SchemeHomOver s πM),
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (U : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S) (X' : FramedPolarisedAbelianScheme g N n S') (hX' : Θ S' X'),
        PolarisedAbelianScheme.IsPullback φ U.val X'.toPolarisedAbelianScheme →
        (ptΘ S' s' X' hX').1 ≫ q = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s U).1) ∧
      (∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (U U' : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S),
        PolarisedAbelianScheme.Satisfying.Iso U U' → pt S s U = pt S s U') ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (U : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S) (U' : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S'),
        PolarisedAbelianScheme.Satisfying.IsPullback φ U U' →
        (pt S' s' U').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s U).1) := by sorry
