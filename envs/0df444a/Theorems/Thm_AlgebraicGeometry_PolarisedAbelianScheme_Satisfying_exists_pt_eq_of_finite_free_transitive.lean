-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_pt_eq_of_finite_free_transitive
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_pt_eq_of_finite_free_transitive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/42bcfe65-0e83-5851-9645-c0c125e0312b
-- title:
--   Every M-point comes from an object satisfying Q
-- statement:
--   Throughout, rings are of type `Type` and schemes live in universe $0$; for a base morphism $s \colon \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and $\pi \colon H \to \operatorname{Spec}\mathcal O$, `SchemeHomOver s π` denotes the type of pairs consisting of a morphism $\varphi \colon \operatorname{Spec} S \to H$ together with the identity $\varphi \mathbin{\text{followed by}} \pi = s$.
--
--   **Data.** Natural numbers $g, N, n$ with $3 \le n$; a commutative ring $\mathcal O$ in which the image of $n$ is a unit; and a predicate $Q$ attaching to every commutative ring $S$ a property of objects of `PolarisedAbelianScheme g (N+1) n S`. An object of `PolarisedAbelianScheme g d n S` consists of a scheme $A$ with a morphism $f \colon A \to \operatorname{Spec} S$, a commutative relative group law $L$ on $f$, an `AbelianSchemePropertyBundle` for $f$, the requirement that every fibre of $f$ have topological Krull dimension $g$, a family $P \colon \mathrm{Fin}(2g) \to$ sections of $f$ that are $n$-torsion for $L$ and that, on every geometric fibre, form a basis of the $n$-torsion (independence of the $n$-ary combinations and generation of all $n$-torsion points), and an invertible module `pol` on $A$ which is very ample in the sense that some projective presentation of it gives a closed immersion, and whose geometric fibrewise $H^0$ has $k$-dimension $d$. An object of `FramedPolarisedAbelianScheme g N n S` is such an object with $d = N+1$ together with a frame: a projective presentation of `pol` relative to $f$ with $N+1$ sections $\sigma_i$, a morphism $A \to \mathbb P^N_S$ over $\operatorname{Spec} S$ compatible with the $\sigma_i$, the requirement that this morphism be a closed immersion, and the requirement that the $\sigma_i$ form a section basis of `pol` over the whole base. The relations `Iso` and `IsPullback` for both notions are the evident ones: an isomorphism of the total spaces over $\operatorname{Spec} S$ compatible with the group laws, carrying the marked sections to the marked sections, and Zariski-locally on the base matching the polarisations (and, in the framed case, commuting with the morphisms to $\mathbb P^N_S$); `IsPullback φ u u'` asserts the existence of a morphism $u'.A \to u.A$ forming a pullback square over $\operatorname{Spec}\varphi$, compatible with group laws and marked sections, with the pullback of `pol` isomorphic to `pol'` (and, in the framed case, compatibility of the frames via the map $\mathbb P^N_{S'} \to \mathbb P^N_S$).
--
--   **Hypotheses on $Q$.** `hQbc`: $Q$ is stable under base change, i.e. if `PolarisedAbelianScheme.IsPullback φ u u'` for a ring homomorphism $\varphi \colon S \to S'$ and $Q\,S\,u$ holds, then $Q\,S'\,u'$ holds. `hQdesc`: $Q$ descends along faithfully flat étale algebra maps: for $S \to S'$ faithfully flat and étale, if $u'$ is a base change of $u$ along $\operatorname{algebraMap} S\,S'$ and $Q\,S'\,u'$ holds, then $Q\,S\,u$ holds.
--
--   **Descent and gluing axioms for polarised abelian schemes** (stated for arbitrary $g, d, n$ with $3 \le n$ and $n$ invertible in the base). `hSHEAF`: for a finite family $r \colon \mathrm{Fin}\,k \to S$ spanning the unit ideal and algebras $B_i$ that are localisations of $S$ away from $r_i$, two assertions hold: (a) given objects $u_i$ over $B_i$ of type $(g,d,n)$ such that for all $i,j$, every localisation $C$ of $S$ away from $r_i r_j$, all $S$-algebra maps $B_i \to C$, $B_j \to C$ and all pullbacks $v_1$ of $u_i$ and $v_2$ of $u_j$ to $C$ one has $v_1 \cong v_2$, there exists $u_0$ over $S$ such that every pullback of $u_0$ to $B_i$ is isomorphic to $u_i$; (b) two objects $u_0, u_0'$ over $S$ whose pullbacks to each $B_i$ are always isomorphic are themselves isomorphic. `hEFF`: for a faithfully flat $S$-algebra $S'$ and an object $u'$ over $S'$ whose two pullbacks to $S' \otimes_S S'$ along `includeLeft` and `includeRight` are always isomorphic, (a) there exists $u$ over $S$ every pullback of which to $S'$ is isomorphic to $u'$, and (b) if $u_1, u_2$ over $S$ have pullbacks $v_1, v_2$ to $S'$ with $v_1 \cong v_2$, then $u_1 \cong u_2$. `hBC`: base changes of objects of type $(g, N+1, n)$ exist along every ring homomorphism.
--
--   **The framed problem $\Theta$.** A predicate $\Theta$ on framed objects over each commutative ring, subject to: `hΘQ`, for every $S$, every morphism $\operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and every framed $X$ with $\Theta\,S\,X$, the underlying polarised abelian scheme satisfies $Q$; `hΘiso`, $\Theta$ is invariant under `FramedPolarisedAbelianScheme.Iso`; `hΘbc`, $\Theta$ is stable under base change along ring homomorphisms (again with an inert base morphism to $\operatorname{Spec}\mathcal O$ in the binder list); `hΘBC`, base changes of framed objects exist along every ring homomorphism.
--
--   **The fine moduli scheme for $\Theta$.** A scheme $H_\Theta$ with a morphism $\pi_\Theta \colon H_\Theta \to \operatorname{Spec}\mathcal O$, and a classifying rule $\mathrm{pt}_\Theta$ sending $S$, a base morphism $s$ and a framed $X$ with $\Theta\,S\,X$ to an element of `SchemeHomOver s πΘ`, subject to: `hpt_iso`, isomorphic framed objects have the same classifying point; `hpt_pullback`, if $\operatorname{Spec}\varphi$ followed by $s$ equals $s'$ and $X'$ over $S'$ is a base change of $X$ along $\varphi$, then the morphism underlying $\mathrm{pt}_\Theta(S',s',X')$ is $\operatorname{Spec}\varphi$ followed by the morphism underlying $\mathrm{pt}_\Theta(S,s,X)$; `hpt_surjective`, every element of `SchemeHomOver s πΘ` is $\mathrm{pt}_\Theta(S,s,X)$ for some framed $X$ with $\Theta\,S\,X$; `hpt_injective`, two framed objects over $S$ with $\Theta$ and the same classifying point are isomorphic. Geometric hypotheses on $\pi_\Theta$: it is separated (`hsep`), quasi-compact (`hqc`) and locally of finite presentation (`hfp`); and `hAF`: every finite subset of $H_\Theta$ is contained in an affine open of $H_\Theta$.
--
--   **The group action.** A finite group $\Gamma$ with a homomorphism $\rho \colon \Gamma \to \operatorname{Aut} H_\Theta$ such that each $\rho(\gamma)$ is a morphism over $\operatorname{Spec}\mathcal O$ (`hρ`), and an action rule `act` sending $S$, a base morphism $s$, an element $\gamma$ and a framed object $X$ to a framed object over $S$, subject to: `hactΘ`, `act` preserves $\Theta$; `hact_val`, `act` leaves the underlying polarised abelian scheme unchanged (so $\Gamma$ moves only the frame); `hact_pt`, the classifying point of $\operatorname{act}(\gamma, X)$ is the classifying point of $X$ followed by $\rho(\gamma)$. Freeness, `hfree`: over a nontrivial ring $S$, if $\Theta\,S\,X$ and $\operatorname{act}(\gamma,X) \cong X$, then $\gamma = 1$. Transitivity, `htrans`: if $\Theta\,S\,X$ and $\Theta\,S\,X'$ and the underlying polarised abelian schemes of $X$ and $X'$ are isomorphic, then there are $m$ and $r \colon \mathrm{Fin}\,m \to S$ spanning the unit ideal such that for each $j$ and all base changes $Y$ of $X$ and $Y'$ of $X'$ to $\operatorname{Localization.Away}(r_j)$ there exists $\gamma \in \Gamma$ with $\operatorname{act}(\gamma, Y) \cong Y'$.
--
--   **Local framability**, `hsurj`: every object $u$ over $S$ with $Q\,S\,u$ admits a faithfully flat $S$-algebra $S'$ and a framed object $X'$ over $S'$ with $\Theta\,S'\,X'$ whose underlying polarised abelian scheme is a base change of $u$ along $\operatorname{algebraMap} S\,S'$.
--
--   **The quotient.** A scheme $M$ with $\pi_M \colon M \to \operatorname{Spec}\mathcal O$ and a morphism $q \colon H_\Theta \to M$ which is $\Gamma$-invariant ($\rho(\gamma)$ followed by $q$ equals $q$, `hq`) and satisfies $q$ followed by $\pi_M$ equals $\pi_\Theta$ (`hqπ`); $q$ is finite, flat, étale and surjective on points (`hqfin`, `hqflat`, `hqet`, `hqsurj`); `hqloc`: for any scheme $T$ and morphisms $t_1, t_2 \colon T \to H_\Theta$ with $t_1$ followed by $q$ equal to $t_2$ followed by $q$, and any point $p$ of $T$, there are $\gamma \in \Gamma$ and an open $U \ni p$ of $T$ with $U \hookrightarrow T \to H_\Theta$ via $t_2$ equal to $U \hookrightarrow T \to H_\Theta \to H_\Theta$ via $t_1$ followed by $\rho(\gamma)$; `hquniq`: for $T$ nonempty and $t \colon T \to H_\Theta$, $t$ followed by $\rho(\gamma)$ equal to $t$ forces $\gamma = 1$.
--
--   **The classifying rule on $M$.** A rule $\mathrm{pt}$ sending $S$, a base morphism $s$ and an element $U$ of `PolarisedAbelianScheme.Satisfying g (N+1) n Q S` — that is, a polarised abelian scheme $U.\mathrm{val}$ of type $(g,N+1,n)$ over $S$ together with $Q\,S\,U.\mathrm{val}$ — to an element of `SchemeHomOver s πM`, subject to the single compatibility `hpt`: whenever $\operatorname{Spec}\varphi$ followed by $s$ equals $s'$, $X'$ is a framed object over $S'$ with $\Theta\,S'\,X'$, and $U.\mathrm{val}$ base-changes along $\varphi$ to the underlying polarised abelian scheme of $X'$, then the morphism underlying $\mathrm{pt}_\Theta(S',s',X')$ followed by $q$ equals $\operatorname{Spec}\varphi$ followed by the morphism underlying $\mathrm{pt}(S,s,U)$.
--
--   **Conclusion.** For every commutative ring $S$, every morphism $s \colon \operatorname{Spec} S \to \operatorname{Spec}\mathcal O$ and every $x$ in `SchemeHomOver s πM` (a morphism $\operatorname{Spec} S \to M$ whose composite with $\pi_M$ is $s$), there exists an element $U$ of `PolarisedAbelianScheme.Satisfying g (N+1) n Q S` with $\mathrm{pt}(S,s,U) = x$. Thus $\mathrm{pt}$ is surjective on $(S,s)$-points; the statement asserts surjectivity only, no uniqueness of $U$ being claimed.
--
--   This is the surjectivity half of the assertion that the quotient $M$ of the frame-rigidified fine moduli scheme $H_\Theta$ by the finite free $\Gamma$-action represents the moduli problem of polarised abelian schemes with full level-$n$ structure satisfying $Q$: every $M$-valued point over $\operatorname{Spec}\mathcal O$ is the classifying point of an object over the test ring. It is used by [`AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_isFineModuli_of_isFineModuli_framed_of_finite_free_transitive_of_three_le), which assembles the fine moduli property of $M$ from the framed one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_Satisfying_exists_pt_eq_of_finite_free_transitive.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.Satisfying.exists_pt_eq_of_finite_free_transitive
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
    ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (x : SchemeHomOver s πM),
      ∃ U : PolarisedAbelianScheme.Satisfying g (N + 1) n Q S, pt S s U = x := by sorry
