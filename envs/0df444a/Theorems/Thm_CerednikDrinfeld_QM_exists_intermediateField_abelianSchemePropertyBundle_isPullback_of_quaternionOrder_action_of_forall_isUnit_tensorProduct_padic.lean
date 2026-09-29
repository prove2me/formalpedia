-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_exists_intermediateField_abelianSchemePropertyBundle_isPullback_of_quaternionOrder_action_of_forall_isUnit_tensorProduct_padic
-- name    : CerednikDrinfeld.QM.exists_intermediateField_abelianSchemePropertyBundle_isPullback_of_quaternionOrder_action_of_forall_isUnit_tensorProduct_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/e00a8347-b8fd-5ef7-a99e-7046c48ffbe0
-- title:
--   Potential good reduction of abelian surfaces with quaternionic multiplication
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a prime $\ell$ such that every non-zero element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_\ell$ is a unit, and let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule satisfying `IsOrder`: it contains $1$, is closed under multiplication, its $\mathbb{Q}$-span is the whole algebra, and it is finitely generated. Let $K\subseteq\overline{\mathbb{Q}}$ be an intermediate field of finite degree over $\mathbb{Q}$, let $f_0\colon A_0\to\operatorname{Spec}K$ be a morphism of schemes equipped with a relative group law $L_0$ (a functorial group structure on the sets $\{\varphi\colon T\to A_0 \mid \varphi\text{ over }t\}$, natural in $T\to\operatorname{Spec}K$) which is commutative, assume `AbelianSchemePropertyBundle` for $f_0$ ($f_0$ smooth, proper, with connected fibres, and admitting a relative group law), and assume every fibre of $f_0$ has topological Krull dimension $2$. Let $\mathrm{act}\colon\Lambda\to\operatorname{End}(A_0)$ consist of endomorphisms over $\operatorname{Spec}K$ which act on $T$-points as group-law homomorphisms, send $1$ to $\mathbb{1}_{A_0}$, satisfy $\mathrm{act}(xy)=\mathrm{act}(y)$ followed by $\mathrm{act}(x)$, and are additive in $\Lambda$ in the sense that $\mathrm{act}(x+y)$ on points is the group-law product of $\mathrm{act}(x)$ and $\mathrm{act}(y)$ on points. Let $B$ be a valuation subring of $\overline{\mathbb{Q}}$ with $B\neq\top$ in which $\ell$ is a unit. Then there is an intermediate field $K'\subseteq\overline{\mathbb{Q}}$ of finite degree over $\mathbb{Q}$ with $K\le K'$ such that: for every ring homomorphism $\varphi\colon B\cap K'\to K'$ inducing the identity on underlying elements of $\overline{\mathbb{Q}}$, and every $f_P\colon P\to\operatorname{Spec}K'$ with relative group law $L_P$ and every $g_P\colon P\to A_0$ making $(g_P,f_P,f_0,\operatorname{Spec}$ of the inclusion $K\hookrightarrow K')$ a pullback square and compatible with the group laws on points, there exist a scheme $\mathcal{A}$, a morphism $f_{\mathcal{A}}\colon\mathcal{A}\to\operatorname{Spec}(B\cap K')$, a commutative relative group law $L_{\mathcal{A}}$ on $f_{\mathcal{A}}$ satisfying `AbelianSchemePropertyBundle`, and $g_{\mathcal{A}}\colon P\to\mathcal{A}$ making $(g_{\mathcal{A}},f_P,f_{\mathcal{A}},\operatorname{Spec.map}\varphi)$ a pullback square and compatible with the group laws on $T$-points. The asserted model over $B\cap K'$ carries no $\Lambda$-action and no fibre-dimension condition, so the conclusion is weaker in shape than the classical statement that the surface with quaternionic multiplication acquires good reduction together with its multiplications.
--
--   This is the $\ell$-adic form of potential good reduction for abelian surfaces with quaternionic multiplication (fake elliptic curves): at any valuation of $\overline{\mathbb{Q}}$ of residue characteristic different from a prime $\ell$ at which the quaternion algebra is a division algebra, a suitable finite extension of the base field produces an abelian scheme model. It is used in the construction of the integral models of fake elliptic curves underlying the Čerednik–Drinfeld description of Shimura curves, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_valuationSubring_inf_of_isPullback_algebraMap_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_valuationSubring_inf_of_isPullback_algebraMap_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_exists_intermediateField_abelianSchemePropertyBundle_isPullback_of_quaternionOrder_action_of_forall_isUnit_tensorProduct_padic.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct

theorem CerednikDrinfeld.QM.exists_intermediateField_abelianSchemePropertyBundle_isPullback_of_quaternionOrder_action_of_forall_isUnit_tensorProduct_padic
    {a b : ℚ} {ℓ : ℕ} [Fact ℓ.Prime] (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] ℚ_[ℓ], x ≠ 0 → IsUnit x)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of ↥K)} (L₀ : RelativeGroupLaw ↥K f₀)
    (hc₀ : L₀.IsCommutative) (h₀ : AbelianSchemePropertyBundle ↥K f₀)
    (hdim : ∀ s : ↥(Spec (CommRingCat.of ↥K)), topologicalKrullDim ↥(f₀.base ⁻¹' {s}) = 2)
    (act : ↥Λ → (A₀ ⟶ A₀)) (act_over : ∀ x : ↥Λ, act x ≫ f₀ = f₀)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥K)) (u v : SchemeHomOver t f₀),
      pushPt (act x) (act_over x) (L₀.mul t u v) = L₀.mul t (pushPt (act x) (act_over x) u) (pushPt (act x) (act_over x) v))
    (act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A₀)
    (act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x)
    (act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥K)) (u : SchemeHomOver t f₀),
      pushPt (act (x + y)) (act_over (x + y)) u = L₀.mul t (pushPt (act x) (act_over x) u) (pushPt (act y) (act_over y) u))
    (B : ValuationSubring (AlgebraicClosure ℚ)) (hB : B ≠ ⊤) (hℓB : IsUnit ((ℓ : ℤ) : ↥B)) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K') (hKK' : K ≤ K'),
      ∀ (φ : ↥(B.toSubring ⊓ K'.toSubring) →+* ↥K')
        (_ : ∀ x : ↥(B.toSubring ⊓ K'.toSubring), ((φ x : ↥K') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
        (P : Scheme.{0}) (fP : P ⟶ Spec (CommRingCat.of ↥K')) (LP : RelativeGroupLaw ↥K' fP)
        (gP : P ⟶ A₀)
        (hgP : CategoryTheory.IsPullback gP fP f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hKK').toRingHom)))
        (_ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K')) (x y : SchemeHomOver t' fP),
          (LP.mul t' x y).1 ≫ gP =
            (L₀.mul (t' ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hKK').toRingHom))
              ⟨x.1 ≫ gP, by rw [Category.assoc, hgP.w, ← Category.assoc, x.2]⟩
              ⟨y.1 ≫ gP, by rw [Category.assoc, hgP.w, ← Category.assoc, y.2]⟩).1),
        ∃ (𝒜 : Scheme.{0}) (f𝒜 : 𝒜 ⟶ Spec (CommRingCat.of ↥(B.toSubring ⊓ K'.toSubring)))
          (L𝒜 : RelativeGroupLaw ↥(B.toSubring ⊓ K'.toSubring) f𝒜) (_ : L𝒜.IsCommutative)
          (_ : AbelianSchemePropertyBundle ↥(B.toSubring ⊓ K'.toSubring) f𝒜)
          (g𝒜 : P ⟶ 𝒜) (hg𝒜 : CategoryTheory.IsPullback g𝒜 fP f𝒜 (Spec.map (CommRingCat.ofHom φ))),
          ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K')) (x y : SchemeHomOver t' fP),
            (LP.mul t' x y).1 ≫ g𝒜 =
              (L𝒜.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
                ⟨x.1 ≫ g𝒜, by rw [Category.assoc, hg𝒜.w, ← Category.assoc, x.2]⟩
                ⟨y.1 ≫ g𝒜, by rw [Category.assoc, hg𝒜.w, ← Category.assoc, y.2]⟩).1 := by sorry
