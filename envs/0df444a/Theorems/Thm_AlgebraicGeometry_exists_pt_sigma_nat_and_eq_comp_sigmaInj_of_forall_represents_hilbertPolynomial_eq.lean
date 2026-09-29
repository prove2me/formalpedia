-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq
-- name    : AlgebraicGeometry.exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/51bbf5e4-349c-5d6d-91cc-ec45786edb27
-- title:
--   Hilbert point in the disjoint union over Hilbert polynomials
-- statement:
--   Let $S$ be a commutative ring, $f : X \to \operatorname{Spec} S$ a morphism of schemes that is flat and locally of finite presentation, and $\mathcal{L}_X$ a module on $X$ that is invertible (each point has a neighbourhood $U$ on which the restriction is isomorphic to the unit module) and satisfies `ClosedImmersionBySections` for $f$, i.e. admits, for some $N$, a projective presentation by $N+1$ global sections whose associated morphism $X \to \operatorname{Proj}$ of the graded polynomial ring in $N+1$ variables over $S$ lies over $f$ and is a closed immersion. Suppose given, for each $P \in \mathbb{Q}[t]$, a scheme $C\,P$ with a morphism $\pi C\,P : C\,P \to \operatorname{Spec} S$, and a rule $ptC$ which to every ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$, and every $\iota : Z \to X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ that is a closed immersion with $Z \to \operatorname{Spec} S'$ flat and locally of finite presentation, and such that for every algebraically closed field $k$ and every $sk : S' \to k$ there is $d_0$ with $\dim_k H^0$ of the geometric fibre at $sk$ of the $d$-th tensor power of the pullback of $\mathcal{L}_X$ to $Z$ equal to $P(d)$ for all $d \ge d_0$, assigns a morphism $\operatorname{Spec} S' \to C\,P$ over $\pi C\,P$ (that is, composing with $\pi C\,P$ gives $s$). Assume $ptC$ is natural: for $\psi : S' \to S''$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$, and data $(Z,\iota)$ over $s$, $(Z'',\iota'')$ over $s''$ both with Hilbert polynomial $P$ in the above sense, together with $e : Z'' \to Z$ exhibiting $Z''$ as the pullback of $Z$ along $\operatorname{Spec}\psi$ and compatible with the base-change map on the ambient pullbacks, the value at $(Z'',\iota'')$ is $\operatorname{Spec}\psi$ followed by the value at $(Z,\iota)$. The conclusion is that there is a rule $pt$ defined on all such $(S',s,Z,\iota)$ with $\iota$ a closed immersion and $Z \to \operatorname{Spec} S'$ flat and locally of finite presentation, with no hypothesis on Hilbert polynomials, whose values are morphisms $\operatorname{Spec} S' \to \coprod_P C\,P$ over $\operatorname{Sigma.desc} \pi C$, such that (i) $pt$ satisfies the same naturality clause with respect to $\psi$, $e$ and the base-change compatibility, and (ii) whenever all geometric fibres of $Z$ have Hilbert polynomial $P$, $pt$ of the datum equals $ptC\,P$ of it followed by the canonical inclusion $C\,P \to \coprod_Q C\,Q$.
--
--   This is the gluing step in the Hilbert-polynomial stratification of the Hilbert functor: from representing objects for the subfunctors of closed subschemes with a fixed fibrewise Hilbert polynomial, it produces a single classifying rule valued in their disjoint union, defined on all flat, finitely presented closed subschemes of $X$ over varying bases. It is used by [`AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections`](thm.html#AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections), where the resulting rule is shown to represent the full functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq.lean

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

theorem AlgebraicGeometry.exists_pt_sigma_nat_and_eq_comp_sigmaInj_of_forall_represents_hilbertPolynomial_eq
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
            (ptC P S'' s'' Z'' ι'' hι'' hfl'' hfp'' hHP'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptC P S' s Z ι hι hfl hfp hHP).1)) :
    ∃ (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{0}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) → SchemeHomOver s (Sigma.desc πC)),

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

      (∀ (P : Polynomial ℚ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z : Scheme.{0}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (hHP : (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
            ((Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s)
              (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
                (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f s)).obj 𝓛X) d) k sk : ℕ) : ℚ) =
              P.eval (d : ℚ))),
        (pt S' s Z ι hι hfl hfp).1 = (ptC P S' s Z ι hι hfl hfp hHP).1 ≫ Sigma.ι C P) := by sorry
