-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections
-- name    : AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/be30f47c-2319-510c-994e-83f5a8ceb0cc
-- title:
--   Hilbert scheme of fixed Hilbert polynomial is proper
-- statement:
--   Let $S$ be a commutative ring, let $f : X \to \operatorname{Spec} S$ be a morphism of schemes that is flat and locally of finite presentation, let $\mathcal L_X$ be a module on $X$ that is invertible (every point has a neighbourhood $U$ on which the restriction of $\mathcal L_X$ is isomorphic to the unit module) and satisfies `ClosedImmersionBySections` for $f$, i.e. for some $N$ there are $N+1$ global sections of $\mathcal L_X$ and a morphism $X \to \mathbb P^N_S$ over $S$, framing $\mathcal L_X$ on the preimages of the standard basic opens and matching the coordinate ratios, which is a closed immersion; let $P \in \mathbb Q[t]$. The assertion is that there exist a scheme $C$, a morphism $\pi_C : C \to \operatorname{Spec} S$ and an assignment $\mathrm{pt}$ which, to each commutative ring $S'$, each $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and each closed immersion $\iota : Z \to X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ whose composite with the projection to $\operatorname{Spec} S'$ is flat and locally of finite presentation and which satisfies the fibrewise condition that for every algebraically closed field $k$ and every ring homomorphism $S' \to k$ there is $d_0$ with $\dim_k H^0$ of the pullback to the geometric fibre of the $d$-th tensor power of $\iota^*\mathcal L_X$ (formed by iterated tensoring starting from the unit module) equal to $P(d)$ for all $d \ge d_0$, attaches a morphism $\operatorname{Spec} S' \to C$ over $\pi_C$, such that: (nat) for $\psi : S' \to S''$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$ and data $(Z,\iota)$ over $S'$, $(Z'',\iota'')$ over $S''$ together with $e : Z'' \to Z$ making $(e, \iota''\!\cdot\!\mathrm{pr}, \iota\!\cdot\!\mathrm{pr}, \operatorname{Spec}\psi)$ a pullback square and $\iota''$ followed by the base-change map compatible with $e$ followed by $\iota$, the point of $Z''$ is $\operatorname{Spec}\psi$ followed by that of $Z$; (surj) every $S'$-point of $C$ over $s$ arises as $\mathrm{pt}$ of such a datum; (inj) two data over the same $s$ with the same point are related by an isomorphism $Z \cong Z'$ compatible with $\iota,\iota'$; and $\pi_C$ is proper and locally of finite presentation.
--
--   This is the representability of the Hilbert scheme $\mathrm{Hilb}^P_{X/S}$ parametrising closed subschemes of a projective $X/S$ that are flat and locally of finite presentation over the base with all geometric Hilbert polynomials equal to a fixed $P$, together with properness and local finite presentation of the structure morphism. It is the single-polynomial piece from which the version indexed by all Hilbert pieces, `exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections`, is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.lean

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

theorem AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections
    (S : Type) [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    [Flat f] [LocallyOfFinitePresentation f]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
    (P : Polynomial ℚ) :
    ∃ (C : Scheme.{0}) (πC : C ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) →
          (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ)) →
          SchemeHomOver s πC),

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
          (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp hHP).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πC),
        ∃ (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
          pt S' s Z ι hι hfl hfp hHP = x) ∧

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
        pt S' s Z ι hι hfl hfp hHP = pt S' s Z' ι' hι' hfl' hfp' hHP' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι) ∧
      IsProper πC ∧ LocallyOfFinitePresentation πC := by sorry
