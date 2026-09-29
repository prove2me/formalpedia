-- Prove2me | Theorems.Thm_AutomorphicForm_integral_twistedConj_map_algEquiv_mul_weight_eq_integral_unipotentGL2_of_biInvariant
-- name    : AutomorphicForm.integral_twistedConj_map_algEquiv_mul_weight_eq_integral_unipotentGL2_of_biInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/60301075-7678-538e-abeb-f67462171425
-- title:
--   Twisted weighted orbital integral equals a unipotent integral
-- statement:
--   Let $K \subseteq L$ be number fields, $v$ a nonzero prime of $\mathcal O_K$ and $w$ a prime of $\mathcal O_L$ lying over $v$, with ramification index $1$; write $F = K_v$, $E = L_w$ for the completions, $\mathcal O_E$ for the valuation ring of $E$ and $K_E \subseteq \mathrm{GL}_2(E)$ for the set of matrices with entries in $\mathcal O_E$ whose inverse also has entries in $\mathcal O_E$. Let $\theta$ be an $F$-algebra automorphism of $E$ whose order equals $[E:F]$, acting on $\mathrm{GL}_2(E)$ entrywise, let $a \neq b$ be units of $F$, let $\alpha,\beta$ be units of $E$ and put $\delta = \mathrm{diag}(\alpha,\beta)$. Assume the $\theta$-twisted centralizer $T = \{t : t\,\delta\,\theta(t)^{-1} = \delta\}$ coincides with the image in $\mathrm{GL}_2(E)$ of the centralizer of $\mathrm{diag}(a,b)$ in $\mathrm{GL}_2(F)$, and let $\tau'$ be a Haar measure on $T$ (Borel $\sigma$-algebra) giving mass $1$ to $\{t \in T : t \in K_E\}$. Let $\Phi : \mathrm{GL}_2(E) \to \mathbb C$ be locally constant with compact support and bi-$K_E$-invariant, $\Phi(k_1 g k_2) = \Phi(g)$ for $k_1,k_2 \in K_E$. Let $s : \mathrm{GL}_2(E) \to \mathbb R$ be nonnegative, Borel measurable and compactly supported, normalised so that $\int_T s(tx)\,d\tau' = 1$ for every $x$ with $\Phi(x^{-1}\delta\,\theta(x)) \neq 0$, and let $\mu_E$ be an additive Haar measure on $E$ with $\mu_E(\mathcal O_E) = 1$. Then, for the Haar measure on $\mathrm{GL}_2(E)$ of mass $1$ on $K_E$ and the weight $\mathrm{weight}(x) = 2\log\!\big(\max(\|x_{00}\|,\|x_{01}\|)\max(\|x_{10}\|,\|x_{11}\|)/\|\det x\|\big)$,
--   $$\int_{\mathrm{GL}_2(E)} \Phi\big(x^{-1}\delta\,\theta(x)\big)\,\mathrm{weight}(x)\,s(x)\,dx = \int_E \Phi\big(\delta\,n(\theta(y) - \beta\alpha^{-1}y)\big)\,2\log\max(1,\|y\|)\,d\mu_E(y),$$
--   where $n(u)$ denotes the unipotent matrix with rows $(1,u)$ and $(0,1)$.
--
--   This is the analytic step in the evaluation of twisted weighted orbital integrals of spherical functions for a split regular twisted-semisimple $\delta$, as in Langlands' base change computation: the Iwasawa decomposition reduces the weighted integral over $\mathrm{GL}_2(E)$, after dividing out by the twisted centralizer by means of the section $s$, to an integral over the unipotent coordinate $y$ against the weight $2\log^+\|y\|$. It is used by the computation of the twisted Hecke-word value and by the comparison of twisted and untwisted weighted terms when the inertia degree equals $[E:F]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_twistedConj_map_algEquiv_mul_weight_eq_integral_unipotentGL2_of_biInvariant.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.integral_twistedConj_map_algEquiv_mul_weight_eq_integral_unipotentGL2_of_biInvariant
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (w.1.adicCompletion L)ˣ)
    (hT : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))))
    (τ' : @Measure (AutomorphicForm.sigmaCentralizer
        (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1)

    (Φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ) (hΦ : AutomorphicForm.IsLocalTestFn L w.1 Φ)
    (hΦK : ∀ g k₁ k₂ : GL (Fin 2) (w.1.adicCompletion L),
      k₁ ∈ AutomorphicForm.localIntegralSet L w.1 → k₂ ∈ AutomorphicForm.localIntegralSet L w.1 →
        Φ (k₁ * g * k₂) = Φ g)

    (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable[AutomorphicForm.localGLBorel L w.1] s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      Φ (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) ≠ 0 →
        ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom)
            (diagUnits2 α β), s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ' = 1)

    [MeasurableSpace (w.1.adicCompletion L)] [BorelSpace (w.1.adicCompletion L)]
    (μE : Measure (w.1.adicCompletion L)) [μE.IsAddHaarMeasure]
    (hμE : μE (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) = 1) :
    ∫ x : GL (Fin 2) (w.1.adicCompletion L),
        Φ (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) *
          ((AutomorphicForm.LocalWeight.weight x : ℝ) : ℂ) * (s x : ℂ)
      ∂(AutomorphicForm.localHaar L w.1) =
      ∫ y : w.1.adicCompletion L,
        Φ (diagUnits2 α β *
            AutomorphicForm.unipotentGL2
              (θ y - ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) * y)) *
          ((2 * Real.log (max 1 ‖y‖) : ℝ) : ℂ) ∂μE := by sorry
