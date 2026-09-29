-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_eq_and_forall_nhds_isTwistedOrbitalIntegral_mul_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_pos_forall_integral_eq_and_forall_nhds_isTwistedOrbitalIntegral_mul_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/14575d2e-00c0-5fca-9997-1bc03af2112f
-- title:
--   Explicit constant in the finite-place twisted orbital comparison
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $2$, let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism of $L$ is an integer power of $\sigma$, let $v$ be a nonzero prime of $\mathcal{O}_K$, write $E = L \otimes_K K_v$ for the completion $K_v$ at $v$, let $c \in K_v^\times$ and let $\delta \in \mathrm{GL}_2(E)$. Assume the scalar matrix $c$ is a norm of $\delta$, i.e. its image in $\mathrm{GL}_2(E)$ equals $y^{-1} N(\delta) y$ for some $y$, where $N(\delta) = \prod_{i<[L:K]} \sigma_{\mathrm{GL}}^{i}(\delta)$ is the norm string and $\sigma_{\mathrm{GL}}$ acts through $\sigma \otimes \mathrm{id}$; assume also that $\delta$ is $\sigma$-conjugate to no scalar, i.e. $\delta \ne x^{-1} \cdot \mathrm{diag}(z,z) \cdot \sigma_{\mathrm{GL}}(x)$ in the sense that no $x$ and unit $z$ of $E$ satisfy $\mathrm{diag}(z,z) = x^{-1}\delta\,\sigma_{\mathrm{GL}}(x)$. Let $T_\delta = \{t : t\delta\sigma_{\mathrm{GL}}(t)^{-1} = \delta\}$ be the twisted centralizer, $\tau'$ a Haar measure on $T_\delta$ for its Borel structure, let $u_0 \in \mathrm{GL}_2(E)$, and let $\tau_S$ be a Haar measure on $S = T_\delta \cap T_{u_0\delta}$. The assertion is that there exists a real $\rho > 0$ with the following two properties. First, for every $w : T_\delta \to \mathbb{R}$ that is nonnegative, measurable, of compact support and satisfies $\int_S w(st)\,d\tau_S(s) = 1$ for all $t \in T_\delta$, one has $\int_{T_\delta} w\,d\tau' = \rho$. Second, for every $\varphi_v : \mathrm{GL}_2(E) \to \mathbb{C}$ that is locally constant with compact support there is a neighbourhood $V$ of $1$ such that for every $u \in V$ lying in $S$ for which $N(u\delta)$ is regular semisimple, meaning $\mathrm{tr}(N(u\delta))^2 - 4\det(N(u\delta))$ is a unit, and for every Haar measure $\tau_u$ on $T_{u\delta}$ whose pushforward to $\mathrm{GL}_2(E)$ along the inclusion agrees with that of $\tau_S$, any value $J$ of the twisted orbital integral of $\varphi_v$ at $u\delta$ relative to $\tau_u$ and any value $I$ at $\delta$ relative to $\tau'$ satisfy $J = \rho I$. Here a complex number is a value of the twisted orbital integral at $\delta'$ relative to a Haar measure $\tau$ when it equals $\int \varphi_v(x^{-1}\delta'\sigma_{\mathrm{GL}}(x))\,w(x)\,d\mu(x)$ against the semi-local Haar measure $\mu$ on $\mathrm{GL}_2(E)$ for some real weight $w$ satisfying the predicate [`AutomorphicForm.IsTwistedSectionFnOn`](def/AutomorphicForm_TwistedOrbital.html#L278) for $\delta'$, $\tau$ and $\varphi_v$.
--
--   This is the finite-place form of the comparison of twisted orbital integrals for a quadratic base change, for a $\sigma$-conjugacy class not meeting the scalars, in which the proportionality constant $\rho$ is pinned down by Weil's integration formula for the subgroup $S$ of the twisted centralizer rather than merely asserted to exist. It is used in deducing the relation between the twisted orbital integral at $\delta$ and the orbital integral of the corresponding scalar, in [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_not_isSigmaConjugate_of_finrank_eq_two`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_orbitalIntegral_scalar_of_not_isSigmaConjugate_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_integral_eq_and_forall_nhds_isTwistedOrbitalIntegral_mul_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_pos_forall_integral_eq_and_forall_nhds_isTwistedOrbitalIntegral_mul_eq_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
        AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) → ℝ,
        (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
         letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
         (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
           ∀ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ),
             ∫ s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                 AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)),
               w ((⟨(s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), (Subgroup.mem_inf.mp s.2).1⟩ :
                 ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) * t) ∂τS = 1) →
        (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
         ∫ t, w t ∂τ' = ρ)) ∧
      ∀ (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ), AutomorphicForm.IsSemiLocalTestFn K L v φv →
        ∃ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), ∀ u ∈ V,
          u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
              AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) →
          AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ (u * δ)) →
          ∀ (τu : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u * δ))
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ))),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)) τu →
            (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K);
              letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ);
              letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                  AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _;
              Measure.map Subtype.val τu = Measure.map Subtype.val τS) →
            ∀ J I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (u * δ) τu φv J →
              AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I → J = (ρ : ℂ) * I := by sorry
