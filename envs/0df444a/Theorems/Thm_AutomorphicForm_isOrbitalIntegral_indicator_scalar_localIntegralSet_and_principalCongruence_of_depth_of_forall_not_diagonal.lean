-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
-- name    : AutomorphicForm.isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/62a2e58b-03bb-5653-ba49-fab2fc17d541
-- title:
--   Orbital integrals of cK₀ and cK(𝔭) indicators at depth m
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$, $K_v$ the completion, $c \in K_v^\times$ and $\varpi \in K_v$ an element of valuation $\mathrm{ofAdd}(-1)$. Let $\gamma_0 \in \mathrm{GL}_2(K_v)$ satisfy [`AutomorphicForm.IsRegularSemisimple`](def/AutomorphicForm_LocalOrbitalBase.html#L402), i.e. $\mathrm{tr}(\gamma_0)^2 - 4\det(\gamma_0)$ is a unit, and assume no conjugate $g^{-1}\gamma_0 g$ has both off-diagonal entries zero. Let $\nu_T$ be a Borel measure on $\mathrm{GL}_2(K_v)$. Let $\gamma$ lie in the centralizer of $\{\gamma_0\}$, be regular semisimple, with $\det(c^{-1}\gamma)$ of valuation $1$, and suppose $c^{-1}\gamma = a\cdot 1 + \varpi^m Y$ with $v(a) \le 1$, $v(\det Y) \le 1$, $v(\mathrm{tr}\,Y) \le 1$, and for no $b$ with $v(b)\le 1$ do both $v(\det(Y - b)) \le v(\varpi)^2$ and $v(\mathrm{tr}(Y-b)) \le v(\varpi)$ hold (depth exactly $m$). Let $\tau$ be a Haar measure on the centralizer of $\gamma$ whose pushforward along the inclusion is $\nu_T$. Put $q = \mathrm{absNorm}(v)$ in $\mathbb C$, let $f_0$ be the indicator of $c\,\cdot$[`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100) (those $g$ with $g$ and $g^{-1}$ integral), $f_1$ the indicator of the translate by $c$ of its subset where all entries of $k-1$ have valuation $<1$, and $\theta = \nu_T\{g \in Z(\gamma_0) : v(\det g) = 1,\ v(\mathrm{tr}\,g) \le 1\}$. Write $\mathrm{Ram}$ for the existence of $t \in Z(\gamma_0)$ with $v(\det t) = \mathrm{ofAdd}(-1)$, and $\mathrm{Near}$ for $m \ge 1$ and $v(a-1) < 1$. Then: if $\mathrm{Ram}$, the predicate [`AutomorphicForm.IsOrbitalIntegral`](def/AutomorphicForm_LocalOrbitalBase.html#L208) holds for $f_0$ with value $(q^{m+1}-1)/((q-1)\theta)$, and, assuming $\mathrm{Near}$, for $f_1$ with value $(q^{m}-1)/((q-1)\theta)$; if $\neg\,\mathrm{Ram}$, it holds for $f_0$ with value $((q+1)q^{m}-2)/((q-1)\theta)$, and, assuming $\mathrm{Near}$, for $f_1$ with value $((q+1)q^{m-1}-2)/((q-1)\theta)$. Here `IsOrbitalIntegral` for $f$ and $I$ means that there is a nonnegative, measurable, compactly supported $w$ with $\int_{Z(\gamma)} w(tx)\,d\tau = 1$ whenever $f(x^{-1}\gamma x) \neq 0$, and $I = \int f(x^{-1}\gamma x)\,w(x)\,d\mu$ for the Haar measure [`AutomorphicForm.localHaar`](def/AutomorphicForm_LocalOrbitalBase.html#L168) attached to the compact open set of integral units.
--
--   This is the local computation of the orbital integrals of the indicator functions of $c\,\mathrm{GL}_2(\mathcal O_v)$ and of $c$ times the principal congruence subgroup at an elliptic (non-split) regular element of depth $m$, the answer being expressed through lattice counts in the Bruhat–Tits tree and split according to whether the associated quadratic extension is ramified. It feeds the bridge to the Shalika germ value, being cited by [`AutomorphicForm.mul_measureReal_torusUnits_eq_neg_div_of_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_forall_not_diagonal`](thm.html#AutomorphicForm.mul_measureReal_torusUnits_eq_neg_div_of_forall_isOrbitalIntegral_eq_add_nhds_scalar_of_forall_not_diagonal), where the four values are compared at two depths.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) (ϖ : v.adicCompletion K)
    (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
    (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))

    (γ : GL (Fin 2) (v.adicCompletion K)) (_hγT : γ ∈ AutomorphicForm.localCentralizer K v γ₀)
    (_hγreg : AutomorphicForm.IsRegularSemisimple γ)
    (_hdet : Valued.v ((((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det) = 1)

    (m : ℕ) (a : v.adicCompletion K) (_ha : Valued.v a ≤ 1) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (_hY : ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + (ϖ ^ m) • Y)
    (_hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (_hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))

    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (_hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (_hτν : @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
        Subtype.val τ = νT) :
    letI := AutomorphicForm.localGLBorel K v

    let q : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
    let f₀ : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
      (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)
    let f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
      {k : GL (Fin 2) (v.adicCompletion K) | k ∈ AutomorphicForm.localIntegralSet K v ∧
          ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}.indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)
    let θ : ℝ := (νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal
    let Ram : Prop := ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)
    let Near : Prop := 1 ≤ m ∧ Valued.v (a - 1) < 1
    (Ram →
      AutomorphicForm.IsOrbitalIntegral K v γ τ f₀ ((q ^ (m + 1) - 1) / ((q - 1) * (θ : ℂ))) ∧
      (Near → AutomorphicForm.IsOrbitalIntegral K v γ τ f₁ ((q ^ m - 1) / ((q - 1) * (θ : ℂ))))) ∧
    (¬ Ram →
      AutomorphicForm.IsOrbitalIntegral K v γ τ f₀ (((q + 1) * q ^ m - 2) / ((q - 1) * (θ : ℂ))) ∧
      (Near → AutomorphicForm.IsOrbitalIntegral K v γ τ f₁ (((q + 1) * q ^ (m - 1) - 2) / ((q - 1) * (θ : ℂ))))) := by sorry
