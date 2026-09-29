-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_framedPt_comp_eq_of_iso_of_finite_free_transitive
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.framedPt_comp_eq_of_iso_of_finite_free_transitive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/422d39da-c9d8-50fc-937b-03ca43613d7a
-- title:
--   Classifying point composed with q depends only on the underlying object
-- statement:
--   Fix natural numbers $g$, $N$, $n$ with $3 \le n$, and a commutative ring $\mathcal O$ in which the image of $n$ is a unit. Throughout, a *polarised abelian scheme of type $(g,d,n)$ over $S$* means a datum `PolarisedAbelianScheme g d n S`: a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law $L$ on $f$, the property bundle `AbelianSchemePropertyBundle S f`, all fibres of $f$ of topological Krull dimension $g$, a family $P_i$ ($i \in \mathrm{Fin}(2g)$) of sections of $f$ killed by $n$ which on every geometric fibre are independent and generate the $n$-torsion (so they frame the $n$-torsion as $(\mathbb Z/n)^{2g}$), and an invertible module $\mathrm{pol}$ on $A$ which embeds $A$ as a closed subscheme by its sections and has $H^0$ of rank $d$ on every geometric fibre. `PolarisedAbelianScheme.Iso` asks for an isomorphism $e$ of the two total spaces over $\operatorname{Spec} S$ compatible with the group laws, carrying the marked points to the marked points, and matching the polarisations locally on the base; `PolarisedAbelianScheme.IsPullback φ u u'` asks for a morphism $u'.A \to u.A$ forming a pullback square with the two structure morphisms and $\operatorname{Spec} φ$, compatible with the group laws and the marked points and pulling $\mathrm{pol}$ back to $\mathrm{pol}$. A *framed* object `FramedPolarisedAbelianScheme g N n S` is a polarised abelian scheme of type $(g,N+1,n)$ together with a `ProjPresentation` of $\mathrm{pol}$ relative to $f$ with $N+1$ sections $\sigma$ — a morphism $\mathrm{toProj}$ to projective $N$-space over $S$ over the base, the sections $\sigma$ trivialising $\mathrm{pol}$ on the corresponding basic opens with the prescribed transition ratios — such that $\mathrm{toProj}$ is a closed immersion and $\sigma$ is a section basis for $\mathrm{pol}$ on the whole of $A$; isomorphism and pullback of framed objects are those of the underlying polarised abelian schemes with the extra requirement that the morphisms to projective space be respected ($e \text{ followed by } X'.\mathrm{toProj} = X.\mathrm{toProj}$, respectively $X'.\mathrm{toProj}$ followed by `ProjSpace.map S S' N` equals the pullback morphism followed by $X.\mathrm{toProj}$).
--
--   The statement is made relative to a predicate $Q$ on polarised abelian schemes of type $(g,N+1,n)$ over arbitrary commutative rings, a predicate $\Theta$ on framed objects of type $(g,N,n)$, and the following groups of hypotheses.
--
--   *(A) Behaviour of $Q$, and base change.* `hQbc`: $Q$ is preserved by base change, i.e. if `PolarisedAbelianScheme.IsPullback φ u u'` for a ring homomorphism $φ : S \to S'$ and $Q\,S\,u$ holds, then so does $Q\,S'\,u'$. `hQdesc`: $Q$ descends along a faithfully flat étale ring extension $S \to S'$: if $u'$ over $S'$ is a base change of $u$ over $S$ and $Q\,S'\,u'$ holds, then $Q\,S\,u$ holds. `hBC`: along any ring homomorphism $φ : S \to S'$ every polarised abelian scheme of type $(g,N+1,n)$ over $S$ admits a base change over $S'$.
--
--   *(B) Descent axioms for polarised abelian schemes* (stated for arbitrary parameters $g$, $d$, $n$ with $3 \le n$ and arbitrary base rings in which $n$ is a unit). `hSHEAF`: for a finite family $r : \mathrm{Fin}\,k \to S$ generating the unit ideal and rings $B_i$ realising the localisations of $S$ away from $r_i$: (i) any family $u_i$ of objects over the $B_i$ which are isomorphic pairwise after further localisation away from $r_i r_j$ (for both $S$-algebra maps into any such localisation $C$, and any base changes there) comes from an object $u_0$ over $S$, in the sense that every base change of $u_0$ to $B_i$ is isomorphic to $u_i$; and (ii) two objects over $S$ whose base changes to each $B_i$ are isomorphic are themselves isomorphic. `hEFF`: for a faithfully flat $S$-algebra $S'$ and an object $u'$ over $S'$ carrying a descent datum (any two base changes of $u'$ to $S' \otimes_S S'$ along the left and right inclusions are isomorphic): (i) there is an object $u$ over $S$ each of whose base changes to $S'$ is isomorphic to $u'$, and (ii) objects $u_1, u_2$ over $S$ with base changes $v_1, v_2$ to $S'$ are isomorphic whenever $v_1$ and $v_2$ are.
--
--   *(C) Behaviour of $\Theta$.* `hΘQ`: $\Theta\,S\,X$ implies $Q\,S$ of the underlying polarised abelian scheme of $X$ (for any morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$). `hΘiso`: $\Theta$ is invariant under `FramedPolarisedAbelianScheme.Iso`. `hΘbc`: $\Theta$ is preserved by base change of framed objects along any ring homomorphism. `hΘBC`: such base changes exist along any ring homomorphism.
--
--   *(D) The classifying scheme for $\Theta$.* A scheme $H_\Theta$ with a morphism $\pi_\Theta : H_\Theta \to \operatorname{Spec}\mathcal O$, and an assignment $\mathrm{pt}_\Theta$ sending each $S$, each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and each framed $X$ with $\Theta\,S\,X$ to an $s$-point of $\pi_\Theta$, that is a morphism $\operatorname{Spec} S \to H_\Theta$ whose composite with $\pi_\Theta$ is $s$. It satisfies: `hpt_iso`, constancy on isomorphism classes; `hpt_pullback`, compatibility with base change, namely if $\operatorname{Spec}φ$ followed by $s$ equals $s'$ and $X'$ over $S'$ is a base change of $X$ over $S$ (both satisfying $\Theta$), then the underlying morphism of $\mathrm{pt}_\Theta(S',s',X')$ equals $\operatorname{Spec}φ$ followed by that of $\mathrm{pt}_\Theta(S,s,X)$; `hpt_surjective`, every $s$-point of $\pi_\Theta$ is $\mathrm{pt}_\Theta(S,s,X)$ for some $\Theta$-framed $X$; and `hpt_injective`, equality of $\mathrm{pt}_\Theta(S,s,X)$ and $\mathrm{pt}_\Theta(S,s,X')$ forces $X \cong X'$ as framed objects.
--
--   *(E) Geometric hypotheses.* $\pi_\Theta$ is separated (`hsep`), quasi-compact (`hqc`) and locally of finite presentation (`hfp`), and every finite subset of points of $H_\Theta$ is contained in an affine open subset (`hAF`).
--
--   *(F) The group action.* A finite group $\Gamma$ with a homomorphism $\rho : \Gamma \to \operatorname{Aut} H_\Theta$ whose automorphisms commute with $\pi_\Theta$ (`hρ`), together with an action $\mathrm{act}$ of $\Gamma$ on framed objects over each pair $(S,s)$ such that: $\Theta$ is preserved (`hactΘ`); the underlying polarised abelian scheme is unchanged, so only the frame is moved (`hact_val`); the classifying point is equivariant, the morphism underlying $\mathrm{pt}_\Theta(S,s,\mathrm{act}\,\gamma\,X)$ being that of $\mathrm{pt}_\Theta(S,s,X)$ followed by $\rho(\gamma)$ (`hact_pt`); the action is free on $\Theta$-framed objects over nontrivial rings, i.e. $\mathrm{act}\,\gamma\,X \cong X$ implies $\gamma = 1$ (`hfree`); and the action is Zariski-locally transitive on frames (`htrans`): if $X$ and $X'$ over $S$ both satisfy $\Theta$ and their underlying polarised abelian schemes are isomorphic, then there are finitely many $r_j \in S$ generating the unit ideal such that for each $j$ and all base changes $Y, Y'$ of $X, X'$ to $\mathrm{Localization.Away}\,(r_j)$ there exists $\gamma \in \Gamma$ with $\mathrm{act}\,\gamma\,Y \cong Y'$ over that localisation (with the induced morphism to $\operatorname{Spec}\mathcal O$).
--
--   *(G) Local existence of frames.* `hsurj`: every polarised abelian scheme $u$ of type $(g,N+1,n)$ over $S$ with $Q\,S\,u$ becomes framed after a faithfully flat extension, i.e. there is a faithfully flat $S$-algebra $S'$ and a framed object $X'$ over $S'$ with $\Theta\,S'\,X'$ whose underlying polarised abelian scheme is a base change of $u$ along $S \to S'$.
--
--   *(H) The quotient target.* A scheme $M$ with $\pi_M : M \to \operatorname{Spec}\mathcal O$ and a morphism $q : H_\Theta \to M$ which is $\Gamma$-invariant, $\rho(\gamma)$ followed by $q$ being $q$ for all $\gamma$ (`hq`), and which lies over $\operatorname{Spec}\mathcal O$, $q$ followed by $\pi_M$ being $\pi_\Theta$ (`hqπ`).
--
--   Under these hypotheses the conclusion asserts: for every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and all framed objects $X_1, X_2$ over $S$ with $\Theta\,S\,X_1$ and $\Theta\,S\,X_2$ whose underlying polarised abelian schemes are isomorphic in the sense of `PolarisedAbelianScheme.Iso`, the morphism underlying $\mathrm{pt}_\Theta(S,s,X_1)$ followed by $q$ equals the morphism underlying $\mathrm{pt}_\Theta(S,s,X_2)$ followed by $q$, as morphisms $\operatorname{Spec} S \to M$.
--
--   This is the well-definedness step for the orbit map: it shows that the composite of the classifying point of a $\Theta$-framed object with a $\Gamma$-invariant morphism $q : H_\Theta \to M$ depends only on the underlying polarised abelian scheme, the frame being removable because $\Gamma$ acts Zariski-locally transitively on frames. It is used in the construction of a fine moduli scheme for $Q$ as the quotient of $H_\Theta$ by the finite free $\Gamma$-action, in [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_framedPt_comp_eq_of_iso_of_finite_free_transitive.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.framedPt_comp_eq_of_iso_of_finite_free_transitive
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
    (hq : ∀ γ : Γ, (ρ γ).hom ≫ q = q) (hqπ : q ≫ πM = πΘ) :
    ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (X₁ X₂ : FramedPolarisedAbelianScheme g N n S) (h₁ : Θ S X₁) (h₂ : Θ S X₂),
      PolarisedAbelianScheme.Iso X₁.toPolarisedAbelianScheme X₂.toPolarisedAbelianScheme →
      (ptΘ S s X₁ h₁).1 ≫ q = (ptΘ S s X₂ h₂).1 ≫ q := by sorry
