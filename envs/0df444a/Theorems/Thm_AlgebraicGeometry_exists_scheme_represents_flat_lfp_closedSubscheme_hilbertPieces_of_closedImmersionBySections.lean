-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections
-- name    : AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/e8e6b199-1202-5564-b9f7-ddf093669034
-- title:
--   Relative Hilbert scheme with quasi-compact Hilbert-polynomial pieces
-- statement:
--   Let $S$ be a commutative ring and let $f : X \to \operatorname{Spec} S$ be a morphism of schemes (in universe $0$) that is flat and locally of finite presentation. Let $\mathcal L_X$ be a module on $X$ which is invertible (every point has a neighbourhood $U$ on which the pullback of $\mathcal L_X$ along $U \hookrightarrow X$ is isomorphic to the unit module) and which admits a closed immersion by sections relative to $f$: for some $N$ there is a projective presentation of $\mathcal L_X$ over $f$, i.e. $N+1$ global sections together with a morphism $X \to \operatorname{Proj}$ of the graded polynomial ring in $N+1$ variables over $S$ compatible with the projection to $\operatorname{Spec} S$, framing the sections locally and matching their ratios, whose structure morphism to $\mathbb P^N_S$ is a closed immersion. Then there exist a scheme $\mathrm{Hilb}$, a morphism $\pi_H : \mathrm{Hilb} \to \operatorname{Spec} S$, and an assignment $\mathrm{pt}$ which to every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every closed immersion $\iota : Z \to X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ with $\iota$ followed by the second projection flat and locally of finite presentation, assigns a morphism $\operatorname{Spec} S' \to \mathrm{Hilb}$ over $\pi_H$ (that is, whose composite with $\pi_H$ is $s$), such that: (i) naturality in the base — given $\psi : S' \to S''$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$, data $(Z,\iota)$ over $s$ and $(Z'',\iota'')$ over $s''$, and $e : Z'' \to Z$ making $Z''$ the pullback of $Z$ along $\operatorname{Spec}\psi$ over the structure morphisms and compatible with the immersions ($\iota''$ followed by the base-change morphism of pullbacks equals $e$ followed by $\iota$), the classifying morphism of $(Z'',\iota'')$ is $\operatorname{Spec}\psi$ followed by that of $(Z,\iota)$; (ii) every morphism $\operatorname{Spec} S' \to \mathrm{Hilb}$ over $\pi_H$ is $\mathrm{pt}$ of some such $(Z,\iota)$; (iii) two data with the same classifying morphism are related by an isomorphism $e : Z \cong Z'$ with $e$ followed by $\iota'$ equal to $\iota$; (iv) $\pi_H$ is separated and locally of finite presentation; and (v) for every $P \in \mathbb Q[T]$ there is an open subscheme $U$ of $\mathrm{Hilb}$ whose underlying set is closed and with $U \hookrightarrow \mathrm{Hilb}$ followed by $\pi_H$ quasi-compact, such that for all $S'$, $s$ and $(Z,\iota)$ as above the image of the classifying morphism on points lies in $U$ if and only if for every algebraically closed field $k$ and every ring homomorphism $S' \to k$ there is $d_0$ with, for all $d \ge d_0$, the $k$-dimension of the global sections of the pullback to the geometric fibre of the $d$-th tensor power of the pullback of $\mathcal L_X$ to $Z$ (the iterated tensor power starting from the unit module) equal to $P(d)$.
--
--   This is the representability of the relative Hilbert functor of flat, finitely presented closed subschemes of a projective $S$-scheme, together with its decomposition into open-and-closed pieces, quasi-compact over the base, cut out by the Hilbert polynomial of the chosen invertible module. It is used in the construction of moduli of polarised abelian schemes, being cited in the corresponding statement for proper flat $f$ with $\mathrm{Hom}$-type point data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections.lean

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

theorem AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections
    (S : Type) [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    [Flat f] [LocallyOfFinitePresentation f]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f) :
    ∃ (Hilb : Scheme.{0}) (πH : Hilb ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) → SchemeHomOver s πH),

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
          (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πH),
        ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)),
          pt S' s Z ι hι hfl hfp = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z Z' : Scheme.{0}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
          (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
          (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s)),
        pt S' s Z ι hι hfl hfp = pt S' s Z' ι' hι' hfl' hfp' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι) ∧
      IsSeparated πH ∧ LocallyOfFinitePresentation πH ∧

      (∀ Pℚ : Polynomial ℚ, ∃ U : Hilb.Opens, IsClosed (U : Set Hilb) ∧ QuasiCompact (U.ι ≫ πH) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)),
          (Set.range (pt S' s Z ι hι hfl hfp).1.base ⊆ (U : Set Hilb) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
                (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                  (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
                Pℚ.eval (d : ℚ))) := by sorry
