-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_iso_of_pt_eq_of_finite_free_transitive
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.iso_of_pt_eq_of_finite_free_transitive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/309c510e-8182-5fdb-92a2-2a771b698a78
-- title:
--   Objects with equal point in the quotient are isomorphic
-- statement:
--   Fix natural numbers $g, N, n$ with $3 \le n$, and a commutative ring $\mathcal{O}$ in which the image of $n$ is a unit. Throughout, a *polarised abelian scheme of type* $(g,d,n)$ over a commutative ring $S$ is a scheme $A$ with a morphism $f : A \to \operatorname{Spec} S$, a commutative relative group law, an abelian-scheme property bundle, all fibres of topological Krull dimension $g$, a family of $2g$ sections $P_i$ killed by $n$ which on every geometric fibre are independent and span the $n$-torsion, together with an invertible module `pol` on $A$ which is very ample in the sense of defining a closed immersion by its sections and whose space of sections on every geometric fibre has rank $d$; a *framed* such object of type $(g,N,n)$ is one of type $(g,N+1,n)$ equipped in addition with a projective presentation of `pol` relative to $f$ with $N+1$ sections whose associated morphism to $\mathbb{P}^N_S$ is a closed immersion and whose sections form a section basis on all of $A$. Isomorphism of polarised abelian schemes means an isomorphism of the underlying schemes over $\operatorname{Spec} S$ that is compatible with the relative group laws on $T$-points, carries the marked sections $P_i$ to the $P_i$, and matches the polarisation modules locally on the base; isomorphism of framed objects requires in addition compatibility with the two morphisms to $\mathbb{P}^N_S$. `IsPullback φ u u'` records that $u'$ is a base change of $u$ along $φ$: a morphism $u'.A \to u.A$ making a pullback square over $\operatorname{Spec} φ$, compatible with the group laws and the marked sections, and identifying the pulled-back polarisation with that of $u'$ (and, in the framed case, the two morphisms to projective space).
--
--   The data are: a predicate $Q$ on polarised abelian schemes of type $(g,N+1,n)$ over arbitrary commutative rings; a predicate $Θ$ on framed polarised abelian schemes of type $(g,N,n)$; a scheme $H_Θ$ with a morphism $π_Θ : H_Θ \to \operatorname{Spec}\mathcal{O}$ and an assignment `ptΘ` sending every ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and every framed object $X$ over $S$ with $Θ\,S\,X$ to a morphism $\operatorname{Spec} S \to H_Θ$ over $s$; a finite group $Γ$ with a homomorphism $ρ : Γ \to \operatorname{Aut} H_Θ$ and an action `act` of $Γ$ on framed objects over each pair $(S,s)$; and a scheme $M$ with $π_M : M \to \operatorname{Spec}\mathcal{O}$, a morphism $q : H_Θ \to M$, and an assignment `pt` sending every $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and every object of `PolarisedAbelianScheme.Satisfying g (N+1) n Q S` (a polarised abelian scheme of type $(g,N+1,n)$ over $S$ together with a proof that it satisfies $Q$) to a morphism $\operatorname{Spec} S \to M$ over $s$.
--
--   The hypotheses fall into the following groups; the content of each group is summarised here.
--
--   *Stability of $Q$* (`hQbc`, `hQdesc`): $Q$ is preserved by base change along an arbitrary ring homomorphism, and descends along a faithfully flat étale ring extension.
--
--   *Descent axioms for polarised abelian schemes* (`hSHEAF`, `hEFF`, `hBC`). `hSHEAF`, stated for arbitrary $g, d, n$ with $3 \le n$ and $n$ invertible in the base ring $S$, asserts for every finite family $r : \mathrm{Fin}\,k \to S$ generating the unit ideal, with $B_i$ a localisation of $S$ away from $r_i$: (a) every family $u_i$ of objects over the $B_i$ whose base changes to any localisation away from $r_i r_j$, along any two $S$-algebra maps from $B_i$ and $B_j$, are isomorphic, is isomorphic to the family of base changes of a single object $u_0$ over $S$; and (b) two objects over $S$ whose base changes to each $B_i$ are isomorphic are isomorphic. `hEFF`, again for arbitrary $g,d,n$ with $3 \le n$ and $n$ invertible in $S$, asserts for a faithfully flat $S$-algebra $S'$ and an object $u'$ over $S'$ carrying a descent datum (its two base changes to $S' \otimes_S S'$ along `includeLeft` and `includeRight` are isomorphic): (a) some object over $S$ has base change to $S'$ isomorphic to $u'$; and (b) two objects over $S$ with isomorphic base changes to $S'$ are isomorphic. `hBC` asserts that base change of objects of type $(g,N+1,n)$ along any ring homomorphism exists.
--
--   *Properties of $Θ$* (`hΘQ`, `hΘiso`, `hΘbc`, `hΘBC`): $Θ$ implies $Q$ for the underlying polarised abelian scheme, is invariant under isomorphism of framed objects, is preserved by base change along arbitrary ring homomorphisms, and base changes of framed objects exist.
--
--   *$(H_Θ, π_Θ, \mathrm{pt}_Θ)$ is a fine moduli scheme for $Θ$* (`hpt_iso`, `hpt_pullback`, `hpt_surjective`, `hpt_injective`): `ptΘ` is unchanged by isomorphism of framed objects; if $\operatorname{Spec}φ$ followed by $s$ equals $s'$ and $X'$ over $S'$ is a base change of $X$ along $φ$, then the point of $X'$ is $\operatorname{Spec}φ$ followed by the point of $X$; every morphism $\operatorname{Spec} S \to H_Θ$ over $s$ arises from some $X$ with $Θ$; and two framed objects over $S$ with the same point are isomorphic.
--
--   *Geometry of $H_Θ$ over $\operatorname{Spec}\mathcal{O}$* (`hsep`, `hqc`, `hfp`, `hAF`): $π_Θ$ is separated, quasi-compact and locally of finite presentation, and every finite subset of $H_Θ$ is contained in an affine open.
--
--   *The $Γ$-action* (`hρ`, `hactΘ`, `hact_val`, `hact_pt`, `hfree`, `htrans`): each automorphism $ρ(γ)$ is a morphism over $\operatorname{Spec}\mathcal{O}$; `act` preserves $Θ$; `act` leaves the underlying polarised abelian scheme unchanged, altering only the frame; the point of $\mathrm{act}\,γ\,X$ is the point of $X$ followed by $ρ(γ)$; the action is free in the sense that over a nontrivial ring, if $\mathrm{act}\,γ\,X$ is isomorphic to $X$ as a framed object with $Θ\,S\,X$, then $γ = 1$; and the action is Zariski-locally transitive on frames: if $X, X'$ over $S$ satisfy $Θ$ and their underlying polarised abelian schemes are isomorphic, then there is a finite family $r : \mathrm{Fin}\,m \to S$ generating the unit ideal such that for each $j$ and all base changes $Y$ of $X$ and $Y'$ of $X'$ to $\mathrm{Localization.Away}\,(r_j)$ there is $γ \in Γ$ with $\mathrm{act}\,γ\,Y$ isomorphic to $Y'$ as framed objects.
--
--   *Framability* (`hsurj`): every object over $S$ satisfying $Q$ becomes, after base change along some faithfully flat $S$-algebra $S'$, the underlying polarised abelian scheme of a framed object over $S'$ satisfying $Θ$.
--
--   *$q$ presents $M$ as the quotient of $H_Θ$ by $Γ$* (`hq`, `hqπ`, `hqfin`, `hqflat`, `hqet`, `hqsurj`, `hqloc`, `hquniq`): $q$ is invariant under the action of $Γ$ on $H_Θ$, $q$ followed by $π_M$ is $π_Θ$, $q$ is finite, flat, étale and surjective on underlying points; any two morphisms $t_1, t_2 : T \to H_Θ$ with $t_1$ followed by $q$ equal to $t_2$ followed by $q$ agree, near each point of $T$ on a suitable open subscheme, after composing $t_1$ with some $ρ(γ)$; and if $T$ is nonempty and $t : T \to H_Θ$ satisfies $t$ followed by $ρ(γ)$ equal to $t$, then $γ = 1$.
--
--   *Compatibility of `pt` with `ptΘ`* (`hpt`): whenever $\operatorname{Spec}φ$ followed by $s$ equals $s'$, $U$ satisfies $Q$ over $S$, $X'$ over $S'$ satisfies $Θ$, and the underlying polarised abelian scheme of $X'$ is the base change of $U$ along $φ$, then the point of $X'$ in $H_Θ$ followed by $q$ equals $\operatorname{Spec}φ$ followed by the point $\mathrm{pt}\,S\,s\,U$ of $M$.
--
--   Under these hypotheses the conclusion is: for every commutative ring $S$, every morphism $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and all $U, U'$ in `PolarisedAbelianScheme.Satisfying g (N+1) n Q S`, if $\mathrm{pt}\,S\,s\,U = \mathrm{pt}\,S\,s\,U'$ as morphisms $\operatorname{Spec} S \to M$ over $s$, then `Satisfying.Iso U U'` holds, that is, the underlying polarised abelian schemes are isomorphic: there is an isomorphism of schemes $e : U.\mathrm{val}.A \cong U'.\mathrm{val}.A$ with $e$ followed by the structure morphism of $U'$ equal to that of $U$, such that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and all $T$-points $x, y$ of $U.\mathrm{val}.A$ over $t$ the product of $x$ and $y$ followed by $e$ equals the product of $x$ followed by $e$ and $y$ followed by $e$; each marked section $P_i$ of $U$ followed by $e$ is the corresponding marked section of $U'$; and every point of $\operatorname{Spec} S$ has an open neighbourhood $V$ such that the pullback of the polarisation of $U'$ along $e$, restricted to the preimage of $V$, is isomorphic to the restriction of the polarisation of $U$ to that preimage.
--
--   This is the injectivity half of the descent of the moduli problem $Q$ from the framed fine moduli scheme $H_Θ$ to the quotient $M = H_Θ/Γ$: objects satisfying $Q$ over $(S,s)$ with the same point of $M$ are isomorphic. It is used, together with the corresponding existence and surjectivity statements, by [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le), which produces a fine moduli scheme for $Q$ out of one for the framed problem $Θ$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_iso_of_pt_eq_of_finite_free_transitive.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.iso_of_pt_eq_of_finite_free_transitive
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

    (hqfin : IsFinite q) (hqflat : Flat q) (hqet : Etale q) (hqsurj : Function.Surjective q.base)
    (hqloc : ∀ {T : Scheme.{0}} (t₁ t₂ : T ⟶ HΘ), t₁ ≫ q = t₂ ≫ q →
      ∀ p : T, ∃ (γ : Γ) (U : T.Opens), p ∈ U ∧ U.ι ≫ t₂ = U.ι ≫ t₁ ≫ (ρ γ).hom)
    (hquniq : ∀ {T : Scheme.{0}} (t : T ⟶ HΘ) (γ : Γ), Nonempty T → t ≫ (ρ γ).hom = t → γ = 1)
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      PolarisedAbelianScheme.Satisfying g (N + 1) n Q S → SchemeHomOver s πM)
    (hpt : (∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
        (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of 𝒪)),
        Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
        ∀ (U : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S) (X' : FramedPolarisedAbelianScheme g N n S') (hX' : Θ S' X'),
        PolarisedAbelianScheme.IsPullback φ U.val X'.toPolarisedAbelianScheme →
        (ptΘ S' s' X' hX').1 ≫ q = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s U).1)) :
    ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (U U' : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S), pt S s U = pt S s U' →
      PolarisedAbelianScheme.Satisfying.Iso U U' := by sorry
