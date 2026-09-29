-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_ptZ_of_isClosedImmersion_iff_qmConditions
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_ptZ_of_isClosedImmersion_iff_qmConditions
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/232b0ad0-85f0-5e53-883d-af0deae2948f
-- title:
--   A closed subscheme of E representing QM structures
-- statement:
--   Fix primes $q \neq q'$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($a>0$ or $b>0$) and, at each height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, its completion is a division algebra exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subset \mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (a finitely generated $\mathbb{Z}$-submodule containing $1$, closed under multiplication and spanning over $\mathbb{Q}$, maximal among such), $\mu \in \Lambda$ with $\mu^2 = -qq'$, $star : \Lambda \to \Lambda$ satisfying $\mu\,star(x) = \bar{x}\mu$, and $\beta : \mathrm{Fin}\,4 \to \Lambda$ a $\mathbb{Z}$-basis of $\Lambda$ (unique integral coordinates). Let $d,m$ be naturals with $m \geq 3$, $R$ a commutative ring in which $m$ is invertible, $X$ a polarised abelian scheme of relative dimension $2$, fibre degree $d$ and level $m$ over $R$, and $\pi_E : E \to \operatorname{Spec} R$ together with a rule $cl$ which, for every ring map $\varphi : R \to R'$, every $(A' \to \operatorname{Spec} R', L')$ with $g : A' \to X.A$ exhibiting it as a group-law pullback of $X.L$ along $\varphi$, and every $\Lambda$-action on $(f',L')$, returns a section of $\pi_E$ over $\operatorname{Spec}\varphi$; assume $cl$ represents $\Lambda$-actions (compatible with further base change, surjective and injective at each base). Let $\iota : Z \to E$ be a closed immersion such that, for every such datum, $cl$ of the $\Lambda$-action factors through $\iota$ if and only if three conditions hold: the trace condition (for every algebraically closed $k$, every $R' \to k$, every finite-dimensional $k$-space $V$ injectively parametrising the tangent vectors at the identity additively and $k$-linearly, and every $\Phi$ inducing the action of $x \in \Lambda$, one has $\mathrm{tr}\,\Phi = n$ whenever $x + \bar{x} = n$); existence of a section $P$ of $f'$ over the identity whose translates by the $\beta j$ match the base changes along $g$ of the level points $X.P\,j$; and existence of a module $polE$ on $A'$ which is canonical polarisation data for $(f',L')$, the action and $star$ (invertible, symmetric, kernel of its Mumford bundle exactly the $2$-torsion, admitting after a faithfully flat base change a square-root decomposition with trivial kernel, with non-zero geometric fibre sections and Rosati-compatible) such that the pullback of $X.pol$ along $g$ is locally on the base isomorphic to $polE \otimes polE \otimes polE$. Then there is a rule $ptZ$ assigning to each ring map $\varphi : R \to T$, each polarised abelian scheme $X'$ of the same type over $T$ which is a pullback of $X$ along $\varphi$, and each QM structure $s'$ on $X'$ (a $\Lambda$-action on $X'.A$ over $X'.f$ by group-law homomorphisms, additive and anti-multiplicative with $1$ acting as the identity, satisfying the trace condition relative to quaternion conjugation, a section $P$ whose $\beta j$-translates are the level points $X'.P\,j$, and canonical polarisation data whose cube is locally isomorphic to $X'.pol$), a morphism $\operatorname{Spec} T \to Z$ over $\operatorname{Spec}\varphi$ with respect to $\iota$ followed by $\pi_E$, such that: $ptZ$ is natural for base change of QM structures along $\psi : T \to T'$ with $\psi \circ \varphi = \varphi'$; for fixed $T, \varphi, X'$ every section of $\iota$ followed by $\pi_E$ over $\operatorname{Spec}\varphi$ is $ptZ$ of some QM structure on $X'$; and $ptZ$ is injective in the QM structure.
--
--   This is the representability step for quaternionic multiplication structures: the closed subscheme $Z \subset E$ cut out by the trace, level-generator and cube-of-canonical-polarisation conditions is shown to be a fine moduli scheme for QM structures on pullbacks of the fixed polarised abelian scheme $X$, in the functor-of-points formulation used throughout the Čerednik–Drinfeld part of the development. Injectivity of the assignment rests on the rigidity statement for polarised abelian schemes with full level structure of level at least $3$, [`AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le); the result feeds into [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_represents_of_representsLatticeActions_of_isUnit_two`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_represents_of_representsLatticeActions_of_isUnit_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_ptZ_of_isClosedImmersion_iff_qmConditions.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_ptZ_of_isClosedImmersion_iff_qmConditions
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (X : PolarisedAbelianScheme 2 d m R)
    (E : Scheme.{0}) (πE : E ⟶ Spec (CommRingCat.of R))
    (cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE)
    (hE : RepresentsLatticeActions Λ X.L E πE cl)
    (Z : Scheme.{0}) (ι : Z ⟶ E) (hι : IsClosedImmersion ι)
    (hZ : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback φ X.L L' g) (i' : LatticeAction Λ f' L'),
        ((∃ y : Spec (CommRingCat.of R') ⟶ Z, y ≫ ι = (cl R' φ L' g hg i').1) ↔
          ((∀ (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k)
              (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f'),
              Function.Injective τ →
              (∀ P : SchemeHomOver (tangentBase k sk) f', P ∈ Set.range τ ↔ IsTangentVector L' k sk P) →
              (∀ v w : V, τ (v + w) = L'.mul (tangentBase k sk) (τ v) (τ w)) →
              (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
              ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (i'.act x) (i'.act_over x) (τ v)) →
              ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
                LinearMap.trace k V Φ = (n : k)) ∧
          (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) f',
            ∀ j : Fin (2 * 2), (pushPt (i'.act (β j)) (i'.act_over (β j)) P).1 ≫ g =
              Spec.map (CommRingCat.ofHom φ) ≫ (X.P j).1) ∧
          (∃ polE : A'.Modules, CerednikDrinfeld.QM.IsCanonicalPolData f' L' i'.act i'.act_over star polE ∧
              LocIsoOnBase f' ((Scheme.Modules.pullback g).obj X.pol) (polE ⊗ polE ⊗ polE))))) :
    ∃ (ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T),
        PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ι ≫ πE)),

      (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : R →+* T) (φ' : R →+* T') (ψ : T →+* T')
          (hψ : ψ.comp φ = φ')
          (X' : PolarisedAbelianScheme 2 d m T) (X'' : PolarisedAbelianScheme 2 d m T')
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ' X X'')
          (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
        QMStructure.IsPullback ψ s' s'' →
          (ptZ T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ X' hX' s').1) ∧

      (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) (ι ≫ πE)),
        ∃ s' : QMStructure Λ star β X', ptZ T φ X' hX' s' = z) ∧

      (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' s'' : QMStructure Λ star β X'),
        ptZ T φ X' hX' s' = ptZ T φ X' hX' s'' → s' = s'') := by sorry
