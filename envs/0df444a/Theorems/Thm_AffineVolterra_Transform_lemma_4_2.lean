-- Prove2me | Theorems.Thm_AffineVolterra_Transform_lemma_4_2
-- name    : AffineVolterra.Transform.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:56:11.054184+00:00
-- url     : https://prove2.me/theorems/3a19e256-597c-43f3-add9-44a6c624b5d0
-- title:
--   Lemma 4.2 — conditional mean of an affine Volterra process
-- statement:
--   Let $X$ be an affine Volterra process and let $R_B$ be the second-kind resolvent of $-KB$, with $E_B=K-R_B*K$. For $0\le t\le T$,
--
--   $$
--   \mathbb E[X_T\mid\mathcal F_t]=\left(I-\int_0^T R_B(s)\,ds\right)x_0+\left(\int_0^T E_B(s)\,ds\right)b^0+\int_0^t E_B(T-s)\sigma(X_s)\,dW_s.
--   $$
--
--   In particular, the unconditional mean is the sum of the first two deterministic terms. The statement gives the integrability of $X_T$ and witnesses the stochastic integral componentwise by Brownian Itô relations.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Lemma 4.2, p. 18

import Mathlib
import Definitions.Def_AffineVolterra_Transform_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace AffineVolterra.Transform

/-- Lemma 4.2, p. 18: the conditional and unconditional means (4.2). -/
theorem lemma_4_2 {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (K R_B : RKernel d) (D : AffineData d)
    (σ : State d → Matrix (Fin d) (Fin d) ℝ) (E : Set (State d))
    (x₀ : State d) (W X : ℝ≥0 → Ω → State d) (T : ℝ≥0)
    (hX : IsAffineVolterra P ℱ K D σ E x₀ W X)
    (hR : IsResolvent (fun s => -kernelRight K (Bmat D) s) R_B) :
    Integrable (X T) P ∧
    ∃ J : Fin d → Fin d → Fin d → ℝ≥0 → Ω → ℝ,
      (∀ i j k, EthierKurtz.HasBrownianItoIntegral P ℱ
        (fun r ω => W r ω k)
        (fun r ω => if r < T then
          EKernel K R_B (T.val - (r : ℝ)) i j * σ (X r ω) j k else 0)
        (J i j k)) ∧
      (∀ t : ℝ≥0, t ≤ T → ∀ᵐ ω ∂P, ∀ i,
        (condExp (ℱ t) P (X T) ω) i =
          (∑ j, ((if i = j then (1 : ℝ) else 0) -
            ∫ s in (0 : ℝ)..T.val, R_B s i j) * x₀ j) +
          (∑ j, (∫ s in (0 : ℝ)..T.val, EKernel K R_B s i j) * D.bv 0 j) +
          ∑ j, ∑ k, J i j k t ω) ∧
      (∀ i, (∫ ω, X T ω i ∂P) =
          (∑ j, ((if i = j then (1 : ℝ) else 0) -
            ∫ s in (0 : ℝ)..T.val, R_B s i j) * x₀ j) +
          (∑ j, (∫ s in (0 : ℝ)..T.val, EKernel K R_B s i j) * D.bv 0 j)) := by sorry

end AffineVolterra.Transform
