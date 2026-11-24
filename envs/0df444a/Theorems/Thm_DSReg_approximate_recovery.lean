-- Prove2me | Theorems.Thm_DSReg_approximate_recovery
-- name    : DSReg.approximate_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:33:03.53526+00:00
-- url     : https://prove2.me/theorems/7f96d9f9-59d6-4f98-a2ad-d06fe8bdd64d
-- title:
--   Theorem 3: approximate recovery under Jacobian perturbation
-- statement:
--   Let the assumptions of Theorem 2 hold with $d\ge2$: $\mu$ is the law of $z$, $g$ is differentiable $\mu$-a.e. with measurable Jacobian $D$, $h(z)=Qz$ $\mu$-a.s. with $Q\in O(d)$, and Structural Diversity and Functional no-cancellation hold. Assume also
--
--   $$\operatorname{ess\,sup}_z\max_r\|D_{r,:}(z)\|_2\le M<\infty.$$
--
--   Let $\widehat D(z)=D(z)+E(z)$ with $E$ measurable and $\operatorname{ess\,sup}_z\max_r\|E_{r,:}(z)\|_2\le\varepsilon$, and for a threshold $\tau>\varepsilon$ let
--
--   $$\widehat N_\tau(R)=\Big|\big\{(r,j):\mu\big(|(\widehat D(z)Q^\top R^\top)_{rj}|>\tau\big)>0\big\}\Big|,\qquad R\in O(d).$$
--
--   If $\delta>0$ satisfies $\tau+\varepsilon<\sigma\,\rho^*(\delta)$, then $\widehat N_\tau$ has a minimizer over $O(d)$, and every minimizer $\widehat R$ satisfies
--
--   $$\min_{P\in SP(d)}\|\widehat RQ-P\|_F<\delta.$$
--
--   **Formalization Note** The essential-supremum bounds are written as almost-everywhere bounds. $\rho^*(\delta)$ is an extended real that is $+\infty$ when $K_\delta=\emptyset$, and the condition $\tau+\varepsilon<\sigma\rho^*(\delta)$ is read in the extended reals.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Section 3.3, Theorem 3, p. 7; proof in Appendix A.4, p. 23

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem approximate_recovery {d p : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (g : (Fin d → ℝ) → Fin p → ℝ) (hdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ g z)
    (hmeas : ∀ r i, Measurable fun z => depJac g z r i)
    (h : (Fin d → ℝ) → Fin d → ℝ) (hhm : Measurable h) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ) (hh : ∀ᵐ z ∂μ, h z = Q.mulVec z)
    (hsd : StructuralDiversity (footprint μ (depJac g)))
    (hfnc : FunctionalNoCancellation μ (depJac g)) (hd : 2 ≤ d)
    (M : ℝ) (hM : ∀ᵐ z ∂μ, ∀ r, vecNorm (fun i => depJac g z r i) ≤ M)
    (E : (Fin d → ℝ) → Matrix (Fin p) (Fin d) ℝ) (hEm : ∀ r i, Measurable fun z => E z r i)
    (ε : ℝ) (hE : ∀ᵐ z ∂μ, ∀ r, vecNorm (fun i => E z r i) ≤ ε)
    (τ : ℝ) (hτ : ε < τ) (δ : ℝ) (hδ : 0 < δ)
    (hcond : ((τ + ε : ℝ) : EReal) < (sigmaMin μ (depJac g) : EReal) * rhoStar μ (depJac g) δ) :
    (∃ R ∈ Matrix.orthogonalGroup (Fin d) ℝ, ∀ R' ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      threshCount μ (fun z => depJac g z + E z) Q τ R ≤
        threshCount μ (fun z => depJac g z + E z) Q τ R') ∧
    ∀ R ∈ Matrix.orthogonalGroup (Fin d) ℝ,
      (∀ R' ∈ Matrix.orthogonalGroup (Fin d) ℝ,
        threshCount μ (fun z => depJac g z + E z) Q τ R ≤
          threshCount μ (fun z => depJac g z + E z) Q τ R') →
      distSP (R * Q) < δ := by sorry

end DSReg
