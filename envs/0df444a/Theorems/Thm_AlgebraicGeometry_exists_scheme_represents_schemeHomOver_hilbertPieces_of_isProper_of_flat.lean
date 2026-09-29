-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
-- name    : AlgebraicGeometry.exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/c09f2e0f-886b-5359-b7b5-a56b45260ec3
-- title:
--   Hom scheme representing S-morphisms, with Hilbert-polynomial pieces
-- statement:
--   Let $S$ be a commutative ring, and let $f : X \to \operatorname{Spec} S$ and $g : Y \to \operatorname{Spec} S$ be morphisms of schemes with $f$ proper, flat and locally of finite presentation and $g$ separated, flat and locally of finite presentation. Let $\mathcal L_X$ be a module over $X$ which is invertible (every point has an open neighbourhood $U$ on which the restriction of $\mathcal L_X$ is isomorphic to the unit sheaf of modules) and which satisfies `Scheme.Modules.ClosedImmersionBySections` over $f$, i.e. for some $N$ there is a `ProjPresentation` of $\mathcal L_X$ relative to $f$ by $N+1$ global sections whose associated morphism $X \to \operatorname{Proj}$ of the homogeneous polynomial ring in $N+1$ variables over $S$ lies over $f$ and is a closed immersion; let $\mathcal L_Y$ satisfy the same two conditions relative to $g$. Then there exist a scheme $H$, a morphism $\pi_H : H \to \operatorname{Spec} S$, and an assignment $pt$ which, for every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every $\varphi : X \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to Y$ with $\varphi$ followed by $g$ equal to the structural morphism of the fibre product to $\operatorname{Spec} S$, produces a pair consisting of a morphism $\operatorname{Spec} S' \to H$ whose composite with $\pi_H$ is $s$, such that: (i) $pt$ is natural, namely for a ring homomorphism $\psi : S' \to S''$ and $s''$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$, the point attached to the base change of $\varphi$ along $\operatorname{Spec}\psi$ (the canonical morphism $X\times_{\operatorname{Spec} S}\operatorname{Spec} S'' \to X\times_{\operatorname{Spec} S}\operatorname{Spec} S'$ followed by $\varphi$) is $\operatorname{Spec}\psi$ followed by the point attached to $\varphi$; (ii) for fixed $S'$ and $s$, every morphism $\operatorname{Spec} S' \to H$ over $s$ arises as $pt$ of some such $\varphi$; (iii) $\varphi$ is determined by its point; (iv) $\pi_H$ is separated and locally of finite presentation; and (v) for every $P \in \mathbb{Q}[T]$ there is an open subscheme $U \subseteq H$ whose underlying set is closed and for which the inclusion followed by $\pi_H$ is quasi-compact, such that for all $S'$, $s$, $\varphi$ as above, the set-theoretic image of the point attached to $\varphi$ is contained in $U$ if and only if for every algebraically closed field $k$ and every ring homomorphism $S' \to k$ there is $d_0$ with: for all $d \ge d_0$, the $k$-dimension, in the sense of `Scheme.Modules.geomFibreH0Finrank` for the projection $X\times_{\operatorname{Spec} S}\operatorname{Spec} S' \to \operatorname{Spec} S'$, of the global sections of the $d$-th tensor power of $(\text{pr}_X^*\mathcal L_X) \otimes (\varphi^*\mathcal L_Y)$ on the geometric fibre equals $P(d)$.
--
--   This is the representability of the functor $S' \mapsto \operatorname{Mor}_S(X_{S'}, Y)$ by a scheme separated and locally of finite presentation over $\operatorname{Spec} S$, in the projective situation where both $X$ and $Y$ carry line bundles given by sections defining closed immersions into projective space, together with the decomposition of the representing scheme into open-and-closed pieces, quasi-compact over the base, cut out by the Hilbert polynomial of the graph. It is used to obtain the Hom scheme in the form without the Hilbert pieces and, in the construction of the relative group law on Jacobians, to produce the scheme of homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat.lean

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

theorem AlgebraicGeometry.exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
    (S : Type) [CommRing S] {X Y : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of S))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated g] [Flat g] [LocallyOfFinitePresentation g]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
    (𝓛Y : Y.Modules) (hY₁ : Scheme.Modules.IsInvertible 𝓛Y) (hY₂ : Scheme.Modules.ClosedImmersionBySections 𝓛Y g) :
    ∃ (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : pullback f s ⟶ Y), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πH),

      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s), pt S' s φ hφ = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ φ' : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ') ∧
      IsSeparated πH ∧ LocallyOfFinitePresentation πH ∧

      (∀ Pℚ : Polynomial ℚ, ∃ U : H.Opens, IsClosed (U : Set H) ∧ QuasiCompact (U.ι ≫ πH) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          (Set.range (pt S' s φ hφ).1.base ⊆ (U : Set H) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
                (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
                  (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X ⊗ (Scheme.Modules.pullback φ).obj 𝓛Y)) d) k sk : ℕ) : ℚ) = Pℚ.eval (d : ℚ))) := by sorry
