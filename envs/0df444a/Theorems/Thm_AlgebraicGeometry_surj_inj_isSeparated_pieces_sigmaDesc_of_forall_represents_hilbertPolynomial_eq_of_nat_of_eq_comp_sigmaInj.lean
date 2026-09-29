-- Prove2me | Theorems.Thm_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj
-- name    : AlgebraicGeometry.surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/d1bf31b5-2753-5c06-b4f8-4b13b2f72a7a
-- title:
--   Representability, separatedness and Hilbert-polynomial strata of coprod_P C_P
-- statement:
--   Throughout, $S$ is a commutative ring, $X$ a scheme (in universe $0$, as are all schemes occurring) and $f : X \to \operatorname{Spec} S$ a morphism that is flat and locally of finite presentation. For a commutative ring $S'$ and a morphism $s : \operatorname{Spec} S' \to \operatorname{Spec} S$, write $X_{S'} := X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ for `pullback f s`, with projections `pullback.fst f s` to $X$ and `pullback.snd f s` to $\operatorname{Spec} S'$. For a morphism $g : Y \to B$ and $h : T \to B$, `SchemeHomOver h g` denotes the subtype of morphisms $\varphi : T \to Y$ with $\varphi$ followed by $g$ equal to $h$; its first component is written $(\cdot)_1$.
--
--   The line bundle datum consists of an object $\mathcal L_X$ of `X.Modules` together with two hypotheses. The hypothesis $hX_1$ states that $\mathcal L_X$ is invertible in the sense of `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ such that the pullback of $\mathcal L_X$ along $U \hookrightarrow X$ is isomorphic to the unit module on $U$. The hypothesis $hX_2$ states `Scheme.Modules.ClosedImmersionBySections 𝓛X f`: there exist $N \in \mathbb N$ and a `ProjPresentation` of $\mathcal L_X$ relative to $f$ with $N+1$ sections whose associated morphism to projective space is a closed immersion. The data of such a presentation (summarised here) are global sections $\sigma_0,\dots,\sigma_N$ of $\mathcal L_X$ and a morphism $\mathrm{toProj} : X \to \operatorname{Proj}$ of the homogeneous coordinate ring of $\mathbb P^N_S$ whose composite with the structure morphism of $\mathbb P^N_S$ is $f$, such that over any open contained in the preimage of the $i$-th standard basic open multiplication by $\sigma_i$ is a bijection from the ring of functions onto the sections of $\mathcal L_X$, and such that the sections $\sigma_i,\sigma_j$ are related by the pullbacks of the coordinate ratios; $hX_2$ requires in addition that $\mathrm{toProj}$ be a closed immersion.
--
--   For a polynomial $P \in \mathbb Q[t]$ and data $(S', s, Z, \iota)$ with $\iota : Z \to X_{S'}$, denote by $H_P(S', s, Z, \iota)$ the Hilbert-polynomial condition appearing repeatedly below: for every algebraically closed field $k$ and every ring homomorphism $s_k : S' \to k$ there is $d_0 \in \mathbb N$ such that for all $d \ge d_0$ the natural number `Scheme.Modules.geomFibreH0Finrank` of the structure morphism $\iota$ followed by `pullback.snd f s`, evaluated at the $d$-fold tensor power built by `Nat.rec` from the unit object of `Z.Modules` by repeatedly tensoring with the pullback of $\mathcal L_X$ along $\iota$ followed by `pullback.fst f s`, at $k$ and $s_k$, equals $P(d)$ after the evident casts to $\mathbb Q$. Here `geomFibreH0Finrank` of a morphism $Z \to \operatorname{Spec} S'$ at a module $M$, a field $k$ and $s_k$ is the $k$-dimension of the module of global sections of the pullback of $M$ to $Z \times_{\operatorname{Spec} S'} \operatorname{Spec} k$, the $k$-structure coming from the structure morphism of that fibre.
--
--   The pieces are given by a family of schemes $C : \mathbb Q[t] \to \mathbf{Sch}$ and morphisms $\pi_{C,P} : C_P \to \operatorname{Spec} S$, together with a rule $\mathrm{pt}_{C}$ which assigns, for each $P$, to every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$, every scheme $Z$ and morphism $\iota : Z \to X_{S'}$ which is a closed immersion and such that $\iota$ followed by `pullback.snd f s` is flat and locally of finite presentation, and every proof of $H_P(S', s, Z, \iota)$, an element of `SchemeHomOver s (πC P)`. Five hypotheses on these data are imposed. (i) $hnatC$: naturality in the base; for each $P$, given commutative rings $S', S''$, a ring homomorphism $\psi : S' \to S''$, morphisms $s, s''$ to $\operatorname{Spec} S$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$, data $(Z,\iota)$ over $s$ and $(Z'',\iota'')$ over $s''$ as above, each closed immersion, flat and locally of finite presentation over the base and each satisfying the condition $H_P$, and a morphism $e : Z'' \to Z$ such that the square formed by $e$, $\iota''$ followed by `pullback.snd f s''`, $\iota$ followed by `pullback.snd f s`, and $\operatorname{Spec}\psi$ is a pullback square, and such that $\iota''$ followed by the base-change morphism `pullback.map f s'' f s` (identity on $X$, $\operatorname{Spec}\psi$ on the base) equals $e$ followed by $\iota$: then the underlying morphism of $\mathrm{pt}_C$ at $(Z'',\iota'')$ equals $\operatorname{Spec}\psi$ followed by the underlying morphism of $\mathrm{pt}_C$ at $(Z,\iota)$. (ii) $hsurjC$: for each $P$, every $S'$, $s$ and every element $x$ of `SchemeHomOver s (πC P)` is of the form $\mathrm{pt}_C$ applied to some $(Z,\iota)$ as above satisfying $H_P$. (iii) $hinjC$: for each $P$, $S'$, $s$ and two such data $(Z,\iota)$, $(Z',\iota')$, both closed immersions, flat and locally of finite presentation over $\operatorname{Spec} S'$ and both satisfying $H_P$, equality of their $\mathrm{pt}_C$-values implies the existence of an isomorphism $e : Z \cong Z'$ with $e$ followed by $\iota'$ equal to $\iota$. (iv) $hproperC$: each $\pi_{C,P}$ is proper. (v) $hlfpC$: each $\pi_{C,P}$ is locally of finite presentation.
--
--   Finally, $\mathrm{pt}$ is a rule assigning, to every commutative ring $S'$, morphism $s : \operatorname{Spec} S' \to \operatorname{Spec} S$, scheme $Z$ and morphism $\iota : Z \to X_{S'}$ which is a closed immersion and is flat and locally of finite presentation over $\operatorname{Spec} S'$ after composition with `pullback.snd f s` — with no Hilbert-polynomial hypothesis — an element of `SchemeHomOver s (Sigma.desc πC)`, i.e. a morphism $\operatorname{Spec} S' \to \coprod_P C_P$ whose composite with the morphism `Sigma.desc πC` induced by the $\pi_{C,P}$ is $s$. Two hypotheses relate $\mathrm{pt}$ to the pieces: $hnat$, naturality of $\mathrm{pt}$ in the base, of exactly the same shape as $hnatC$ but with the hypotheses $H_P$ deleted; and $hconst$, stating that for every $P$ and every datum $(S', s, Z, \iota)$ as above which satisfies $H_P$, the underlying morphism of $\mathrm{pt}$ equals the underlying morphism of $\mathrm{pt}_C$ at $P$ followed by the coprojection `Sigma.ι C P`.
--
--   Under these hypotheses the conclusion is a fivefold conjunction concerning the morphism `Sigma.desc πC` from $\coprod_P C_P$ to $\operatorname{Spec} S$.
--
--   First (surjectivity): for every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every element $x$ of `SchemeHomOver s (Sigma.desc πC)` there exist $Z$ and $\iota : Z \to X_{S'}$, a closed immersion, flat and locally of finite presentation over $\operatorname{Spec} S'$, with $\mathrm{pt}$ at this datum equal to $x$.
--
--   Second (injectivity up to isomorphism of subschemes): for every $S'$, $s$ and data $(Z,\iota)$, $(Z',\iota')$, both closed immersions into $X_{S'}$ and both flat and locally of finite presentation over $\operatorname{Spec} S'$, equality of the two $\mathrm{pt}$-values implies the existence of an isomorphism $e : Z \cong Z'$ with $e$ followed by $\iota'$ equal to $\iota$.
--
--   Third: `Sigma.desc πC` is separated. Fourth: `Sigma.desc πC` is locally of finite presentation.
--
--   Fifth (the Hilbert-polynomial strata): for every $P_{\mathbb Q} \in \mathbb Q[t]$ there exists an open subscheme $U$ of $\coprod_P C_P$ such that the underlying subset of $U$ is closed in $\coprod_P C_P$, the inclusion $U \hookrightarrow \coprod_P C_P$ followed by `Sigma.desc πC` is quasi-compact, and for every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every $(Z,\iota)$ with $\iota$ a closed immersion into $X_{S'}$, flat and locally of finite presentation over $\operatorname{Spec} S'$, the set-theoretic image of the base map of the morphism underlying $\mathrm{pt}$ at this datum is contained in $U$ if and only if $H_{P_{\mathbb Q}}(S', s, Z, \iota)$ holds.
--
--   This is the assembly step which passes from a family of representing schemes $C_P$, one for each Hilbert polynomial $P$, to their coproduct $\coprod_P C_P$ as a single scheme carrying the full functor of flat, finitely presented closed subschemes of $X_{S'}$, together with the open-and-closed stratification by Hilbert polynomial and the separatedness and finite-presentation properties of its structure morphism. It is used by [`AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections`](thm.html#AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections), the existence statement for the Hilbert scheme of a flat, locally finitely presented $X/S$ with an invertible module that is very ample in the sense of closed immersion by sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MonoidalCategory

theorem AlgebraicGeometry.surj_inj_isSeparated_pieces_sigmaDesc_of_forall_represents_hilbertPolynomial_eq_of_nat_of_eq_comp_sigmaInj
    (S : Type) [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    [Flat f] [LocallyOfFinitePresentation f]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
    (C : Polynomial ℚ → Scheme.{0}) (πC : ∀ P : Polynomial ℚ, C P ⟶ Spec (CommRingCat.of S))
    (ptC : ∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
          SchemeHomOver s (πC P))
    (hnatC : ∀ (P : Polynomial ℚ),
        (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
            (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
            (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
            (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
            (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
            (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ)))
            (Z'' : Scheme.{0}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
            (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
            (hHP'' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S'' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι'' ≫ pullback.snd f s'')
                (Nat.rec (motive := fun _ => Z''.Modules) (𝟙_ Z''.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι'' ≫ pullback.fst f s'')).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ)))
            (e : Z'' ⟶ Z),
            IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
            ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
                (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
            (ptC P S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptC P S' s Z ι hι hfl hfp hHP).1))
    (hsurjC : ∀ (P : Polynomial ℚ),
        (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s (πC P)),
          ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
            (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
            (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ))),
            ptC P S' s Z ι hι hfl hfp hHP = x))
    (hinjC : ∀ (P : Polynomial ℚ),
        (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
            (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
            (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
            (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
            (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s))
            (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ)))
            (hHP' : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι' ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z'.Modules) (𝟙_ Z'.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι' ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ))),
          ptC P S' s Z ι hι hfl hfp hHP = ptC P S' s Z' ι' hι' hfl' hfp' hHP' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι))
    (hproperC : ∀ P : Polynomial ℚ, IsProper (πC P)) (hlfpC : ∀ P : Polynomial ℚ, LocallyOfFinitePresentation (πC P))
    (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) → SchemeHomOver s (Sigma.desc πC))
    (hnat :

        (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
            (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
            (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
            (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
            (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
            (Z'' : Scheme.{0}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
            (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
            (e : Z'' ⟶ Z),

            IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
            ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
                (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
            (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp).1))
    (hconst :

        (∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
            (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
            (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
            (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                P.eval (d : ℚ))),
          (pt S' s Z ι hι hfl hfp).1 = (ptC P S' s Z ι hι hfl hfp hHP).1 ≫ Sigma.ι C P)) :

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s (Sigma.desc πC)),
        ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)),
          pt S' s Z ι hι hfl hfp = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
          (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
          (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s)),
        pt S' s Z ι hι hfl hfp = pt S' s Z' ι' hι' hfl' hfp' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι) ∧
      IsSeparated (Sigma.desc πC) ∧ LocallyOfFinitePresentation (Sigma.desc πC) ∧

      (∀ Pℚ : Polynomial ℚ, ∃ U : (∐ C).Opens, IsClosed (U : Set ↥(∐ C)) ∧ QuasiCompact (U.ι ≫ (Sigma.desc πC)) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)),
          (Set.range (pt S' s Z ι hι hfl hfp).1.base ⊆ (U : Set ↥(∐ C)) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                Pℚ.eval (d : ℚ))) := by sorry
