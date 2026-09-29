-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/221a6695-3753-5c1e-b358-ba939aaa8822
-- title:
--   Unique descent of homomorphic endomorphisms along a connected base change
-- statement:
--   Fix $N \in \mathbb{N}$, rationals $a,b$ and a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$. Let $k_0$ be an algebraically closed field and $A_0$ a fake elliptic curve of level $\Lambda$, $N$ over $k_0$, i.e. a scheme $A_0.A$ with structure morphism $A_0.f$ to $\operatorname{Spec} k_0$, a commutative relative group law $A_0.L$ on points, the abelian-scheme property bundle, two-dimensional fibres, a $\Lambda$-action and level data. Assume given a module $\mathcal{L}$ on $A_0.A$ that is invertible (locally isomorphic to the unit sheaf) and satisfies `ClosedImmersionBySections` for $A_0.f$, i.e. admits a projective presentation by finitely many global sections whose associated morphism to the relevant $\operatorname{Proj}$ over $k_0$ is a closed immersion. Let $Bb$ be a nontrivial commutative ring whose only idempotents are $0$ and $1$, $\psi_b : k_0 \to Bb$ a ring homomorphism, $A_b$ a fake elliptic curve of the same level over $Bb$ and $g_A : A_b.A \to A_0.A$ a morphism exhibiting $A_b$ as a pull-back of $A_0$ along $\psi_b$ in the sense of `IsPullbackVia`: the square formed by $g_A$, $A_b.f$, $A_0.f$ and $\operatorname{Spec}(\psi_b)$ is a pull-back, $g_A$ carries products for $A_b.L$ to products for $A_0.L$ on points, it intertwines the two $\Lambda$-actions, and it carries points factoring through the level morphism of $A_b$ to points factoring through that of $A_0$. Finally let $\varphi : A_b.A \to A_b.A$ satisfy $A_b.f \circ \varphi = A_b.f$ and be a homomorphism on points: for every scheme $T$, every $t : T \to \operatorname{Spec} Bb$ and all $T$-points $P, Q$ of $A_b$ over $t$, post-composition with $\varphi$ takes $A_b.L.\mathrm{mul}\,t\,P\,Q$ to the product of the images. Then there is a morphism $\varphi_0 : A_0.A \to A_0.A$ with $A_0.f \circ \varphi_0 = A_0.f$, again a homomorphism on points for $A_0.L$ over every base $t : T \to \operatorname{Spec} k_0$, such that $\varphi$ followed by $g_A$ equals $g_A$ followed by $\varphi_0$; moreover any morphism $\varphi_0'$ over $k_0$ that is a homomorphism on points and satisfies $\varphi$ followed by $g_A$ equals $g_A$ followed by $\varphi_0'$ coincides with $\varphi_0$.
--
--   This is the rigidity statement that endomorphisms of an abelian scheme over a base with no nontrivial idempotents, obtained by base change from an algebraically closed field, are constant: they descend to the field, and do so uniquely. It is the descent step used in the comparison of $\Lambda$-actions on fake elliptic curves, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_act_comp_eq_of_isPullbackVia_of_forall_isIdempotentElem_of_closedImmersionBySections_of_isAlgClosed); the projectivity input `ClosedImmersionBySections` is what makes the Hom-scheme available, and uniqueness comes from its formal unramifiedness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed.lean

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMIsogeny

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_comp_unique_of_isPullbackVia_of_forall_isIdempotentElem_of_isAlgClosed
    {N : ℕ} {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (A₀ : FakeEllipticCurve Λ N k₀)

    (𝓛 : A₀.A.Modules) (h𝓛₁ : Scheme.Modules.IsInvertible 𝓛) (h𝓛₂ : Scheme.Modules.ClosedImmersionBySections 𝓛 A₀.f)
    (Bb : Type) [CommRing Bb] [Nontrivial Bb] (ψb : k₀ →+* Bb) (hBb : ∀ x : Bb, IsIdempotentElem x → x = 0 ∨ x = 1)
    (Ab : FakeEllipticCurve Λ N Bb) (gA : Ab.A ⟶ A₀.A) (hAb : FakeEllipticCurve.IsPullbackVia ψb A₀ Ab gA)
    (φ : Ab.A ⟶ Ab.A) (hφ : φ ≫ Ab.f = Ab.f)
    (hφhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of Bb)) (P Q : SchemeHomOver t Ab.f),
      mapPt φ hφ (Ab.L.mul t P Q) = Ab.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) :
    ∃ (φ₀ : A₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = A₀.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
        mapPt φ₀ hφ₀ (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q)) ∧
      φ ≫ gA = gA ≫ φ₀ ∧
      ∀ (φ₀' : A₀.A ⟶ A₀.A) (hφ₀' : φ₀' ≫ A₀.f = A₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
          mapPt φ₀' hφ₀' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀' hφ₀' P) (mapPt φ₀' hφ₀' Q)) →
        φ ≫ gA = gA ≫ φ₀' → φ₀' = φ₀ := by sorry
