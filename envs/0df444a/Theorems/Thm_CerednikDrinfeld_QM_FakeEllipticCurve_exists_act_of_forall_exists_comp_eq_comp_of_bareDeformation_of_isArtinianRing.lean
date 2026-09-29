-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/4792f054-17b9-5c7d-9d45-ccf4a196f6b7
-- title:
--   Lifting the Λ-action to a bare deformation
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $N\in\mathbb{N}$, let $S$ be an Artinian local commutative ring and $S_0$ a commutative $S$-algebra such that $\mathrm{algebraMap}\,S\,S_0$ is surjective with nilpotent kernel ideal. Let $E_0$ be a fake elliptic curve over $S_0$ for the data $(\Lambda,N)$ — in particular a scheme $E_0.A$ over $\operatorname{Spec} S_0$ carrying a commutative relative group law, the abelian-scheme property bundle, two-dimensional fibres, level data, and an action $x\mapsto E_0.\mathrm{act}\,x$ of $\Lambda$ by endomorphisms over the base satisfying the unit, multiplicativity, additivity, homomorphism and trace conditions — and let $D$ be a bare deformation of $(E_0.f,E_0.L)$ to $S$: a scheme $D.A$ over $\operatorname{Spec} S$ with commutative relative group law $D.L$ and property bundle, together with $D.g : E_0.A \to D.A$ making the square with $\operatorname{Spec}$ of $\mathrm{algebraMap}\,S\,S_0$ cartesian and compatible with the group laws on points. Assume that for each $x\in\Lambda$ there exists some $\varphi : D.A \to D.A$ over $\operatorname{Spec} S$ with $E_0.\mathrm{act}\,x$ followed by $D.g$ equal to $D.g$ followed by $\varphi$. Then there is a family $\mathrm{act} : \Lambda \to \operatorname{End}(D.A)$ of endomorphisms over $\operatorname{Spec} S$ such that: for every $x$, every scheme $T$, every $t : T \to \operatorname{Spec} S$ and all $T$-points $P,Q$ of $D.f$ over $t$, postcomposition with $\mathrm{act}\,x$ carries $D.L.\mathrm{mul}\,t\,P\,Q$ to $D.L.\mathrm{mul}$ of the images of $P$ and $Q$; $\mathrm{act}\,1 = \mathrm{id}$ whenever $1\in\Lambda$; $\mathrm{act}(xy) = \mathrm{act}\,y$ followed by $\mathrm{act}\,x$ whenever $xy\in\Lambda$; postcomposition with $\mathrm{act}(x+y)$ on a point $P$ equals the $D.L$-sum of the postcompositions with $\mathrm{act}\,x$ and $\mathrm{act}\,y$; and $E_0.\mathrm{act}\,x$ followed by $D.g$ equals $D.g$ followed by $\mathrm{act}\,x$ for all $x\in\Lambda$.
--
--   This is the rigidity step in the deformation theory of fake elliptic curves: from the mere existence, for each quaternion in $\Lambda$, of some lift of the corresponding endomorphism to the deformation, one obtains a canonical lift which is simultaneously unital, multiplicative, additive and a homomorphism for the relative group law — precisely the four action axioms of a fake elliptic curve — and which is compatible with the given action on the closed fibre. It is used in the analysis of bare deformations over the dual numbers, where isomorphism criteria for deformations of fake elliptic curves are established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_act_of_forall_exists_comp_eq_comp_of_bareDeformation_of_isArtinianRing
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    (E₀ : FakeEllipticCurve Λ N S₀) (D : BareDeformation E₀.f E₀.L S)
    (hlift : ∀ x : ↥Λ, ∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ E₀.act x ≫ D.g = D.g ≫ φ) :
    ∃ (act : ↥Λ → (D.A ⟶ D.A)) (act_over : ∀ x : ↥Λ, act x ≫ D.f = D.f),
      ((∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t D.f),
          pushPt (act x) (act_over x) (D.L.mul t P Q) =
            D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)) ∧
        (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 D.A) ∧
        (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
        (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t D.f),
          pushPt (act (x + y)) (act_over (x + y)) P =
            D.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))) ∧
      (∀ x : ↥Λ, E₀.act x ≫ D.g = D.g ≫ act x) := by sorry
