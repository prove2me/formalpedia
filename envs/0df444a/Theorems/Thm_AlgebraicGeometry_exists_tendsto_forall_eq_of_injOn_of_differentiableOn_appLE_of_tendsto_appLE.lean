-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE
-- name    : AlgebraicGeometry.exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/14a98dda-d8c1-5262-8317-16918c2a81f9
-- title:
--   Injective holomorphic chart lifts evaluation-convergent sequences of ℂ-points
-- statement:
--   Let $Y$ be a scheme and $g : Y \to \operatorname{Spec}\mathbb{C}$ a morphism that is `SmoothOfRelativeDimension 1`, let $W$ be an open subset of the upper half-plane, and let $h$ assign to each point of the upper half-plane a $\mathbb{C}$-point of $Y$ over $g$, that is, a pair consisting of a morphism $\operatorname{Spec}\mathbb{C} \to Y$ together with a proof that composing it with $g$ gives the identity of $\operatorname{Spec}\mathbb{C}$; assume $h$ is injective on $W$. The holomorphy hypothesis states: for every open $U \subseteq Y$ and every $s \in \Gamma(Y,U)$, the set of $z \in \mathbb{C}$ with $\operatorname{Im} z > 0$, $\mathrm{ofComplex}\,z \in W$ and $h(\mathrm{ofComplex}\,z)$ factoring through $U$ (i.e. $\top \le h(\mathrm{ofComplex}\,z)^{-1}U$) is open in $\mathbb{C}$, and there is $F : \mathbb{C} \to \mathbb{C}$, complex differentiable on that set, whose value at each such $z$ is the scalar obtained from $s$ by the `appLE` map of $h(\mathrm{ofComplex}\,z)$ for $U$ and $\top$, read through the isomorphism $\Gamma(\operatorname{Spec}\mathbb{C}) \cong \mathbb{C}$. Let $\tau_* \in W$ and let $\sigma : \mathbb{N} \to Y(\mathbb{C})$ (again as morphisms over $g$) satisfy: for every affine open $U$ with $h(\tau_*)$ in $U$, there are $n_0$ and a witness that $\sigma_n$ lies in $U$ for all $n \ge n_0$, such that for each $f \in \Gamma(Y,U)$ the sequence of values $f(\sigma_n)$ (set to $0$ for $n < n_0$) tends to $f(h(\tau_*))$. Then there exist $\tau' : \mathbb{N} \to$ upper half-plane and $n_0 \in \mathbb{N}$ with $\tau'_n \in W$ and $h(\tau'_n) = \sigma_n$ for all $n \ge n_0$, and $\tau'_n \to \tau_*$.
--
--   This is the statement that an injective holomorphic parametrisation of a smooth relative-dimension-one complex scheme by an open subset of the upper half-plane is, near a given point, an open map onto the evaluation topology: sequences of $\mathbb{C}$-points converging in the sense of values of regular functions on affine neighbourhoods eventually lie in the image of the chart, with preimages converging. It is the analytic ingredient of a closedness argument in the Čerednik–Drinfel'd fine moduli setting, being used in [`CerednikDrinfeld.QM.IsFineModuli.isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic`](thm.html#CerednikDrinfeld.QM.IsFineModuli.isClosed_setOf_exists_smul_latt_eq_qmPeriodLattice_of_isProper_of_analytic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra Filter Topology

theorem AlgebraicGeometry.exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE
    (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of ℂ)) (hsm : SmoothOfRelativeDimension 1 g)
    (W : Set UpperHalfPlane) (hW : IsOpen W)
    (h : UpperHalfPlane → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (hinj : Set.InjOn h W)

    (hHOL : ∀ (U : Y.Opens) (s : Γ(Y, U)),
      IsOpen {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
      ∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F
          {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
        ∀ (z : ℂ), 0 < z.im → UpperHalfPlane.ofComplex z ∈ W →
          ∀ hU : ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U,
            F z = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h (UpperHalfPlane.ofComplex z)).1.appLE U ⊤ hU) s))
    (τs : UpperHalfPlane) (hτs : τs ∈ W)

    (σ : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g)
    (hconv : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hQ : ⊤ ≤ (h τs).1 ⁻¹ᵁ U),
      ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (σ n).1 ⁻¹ᵁ U,
        ∀ f : Γ(Y, U),
          Tendsto (fun n : ℕ => if hn : n₀ ≤ n then
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((σ n).1.appLE U ⊤ (hP n hn)) f) else 0)
            atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h τs).1.appLE U ⊤ hQ) f)))) :
    ∃ (τ' : ℕ → UpperHalfPlane) (n₀ : ℕ), (∀ n, n₀ ≤ n → τ' n ∈ W ∧ h (τ' n) = σ n) ∧
      Tendsto τ' atTop (𝓝 τs) := by sorry
