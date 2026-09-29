-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_isClosedImmersion_iff_exists_level_generator_lfp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/49ccb922-7ef3-513f-a9b0-9f89d220fb7e
-- title:
--   Level generation by one point cuts out a closed subscheme of E
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order (it contains $1$, is closed under multiplication, spans the algebra over $\mathbb{Q}$ and is finitely generated), and $\beta : \mathrm{Fin}(2\cdot 2) \to \Lambda$ such that every element of $\Lambda$ is uniquely an integral combination of the $\beta_j$, i.e. a $\mathbb{Z}$-basis of $\Lambda$. Let $d, m$ be naturals, $R$ a commutative ring, and $X$ a `PolarisedAbelianScheme 2 d m R`: a scheme $X.A \to \operatorname{Spec} R$ with a commutative relative group law $X.L$, the abelian-scheme property bundle, fibres of topological Krull dimension $2$, four sections $X.P_j$ over the identity of $\operatorname{Spec} R$ which are $m$-torsion and give a full level-$m$ structure on geometric fibres, and an invertible module whose sections give a closed immersion and whose geometric fibre $H^0$-rank is $d$. Let $\pi_E : E \to \operatorname{Spec} R$ and let $\mathrm{cl}$ assign, to each ring homomorphism $\varphi : R \to R'$, each $f' : A' \to \operatorname{Spec} R'$ with relative group law $L'$ and each $g : A' \to X.A$ exhibiting $(f', L')$ as the pullback of $(X.f, X.L)$ along $\varphi$ in the sense of `IsGroupPullback`, and each action of $\Lambda$ on $(f', L')$ in the sense of `LatticeAction`, a section of $\pi_E$ over $\operatorname{Spec}\varphi$; assume `RepresentsLatticeActions`, i.e. $\mathrm{cl}$ is compatible with further base change and is bijective onto such sections. Then there are a scheme $Z_4$ and a morphism $\iota : Z_4 \to E$ which is a closed immersion and locally of finite presentation, such that for all such $\varphi, A', f', L', g, hg$ and every lattice action $i'$, the point $\mathrm{cl}(R', \varphi, L', g, hg, i')$ factors through $\iota$ if and only if there is a section $P$ of $f'$ over the identity of $\operatorname{Spec} R'$ with $i'(\beta_j) \circ P$ followed by $g$ equal to $\operatorname{Spec}\varphi$ followed by $X.P_j$, for each $j \in \mathrm{Fin}(2\cdot 2)$.
--
--   This identifies the locus in the scheme $E$ of quaternionic actions on base changes of the polarised abelian surface $X$ where the marked level sections are exactly the $\beta_j$-translates of a single $R'$-point, as a closed subscheme, locally of finite presentation over $E$. It is the closedness and finite-presentation input for the construction of the quaternionic moduli data used in the Čerednik–Drinfeld part of the argument, and is cited by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_isClosedImmersion_iff_trace_and_exists_level_generator_and_exists_isCanonicalPolData_of_isUnit_two`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_isClosedImmersion_iff_trace_and_exists_level_generator_and_exists_isCanonicalPolData_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isClosedImmersion_iff_exists_level_generator_lfp.lean

import Definitions.Def_CerednikDrinfeld_QMLatticeAction
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM
  AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_isClosedImmersion_iff_exists_level_generator_lfp
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    {d m : ℕ} {R : Type} [CommRing R] (X : PolarisedAbelianScheme 2 d m R)
    {E : Scheme.{0}} {πE : E ⟶ Spec (CommRingCat.of R)}
    {cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE}
    (hE : RepresentsLatticeActions Λ X.L E πE cl) :
    ∃ (Z₄ : Scheme.{0}) (ι : Z₄ ⟶ E), IsClosedImmersion ι ∧ LocallyOfFinitePresentation ι ∧
      ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback φ X.L L' g) (i' : LatticeAction Λ f' L'),
        ((∃ y : Spec (CommRingCat.of R') ⟶ Z₄, y ≫ ι = (cl R' φ L' g hg i').1) ↔
          (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f',
            ∀ j : Fin (2 * 2), (pushPt (i'.act (β j)) (i'.act_over (β j)) P).1 ≫ g =
              Spec.map (CommRingCat.ofHom φ) ≫ (X.P j).1)) := by sorry
