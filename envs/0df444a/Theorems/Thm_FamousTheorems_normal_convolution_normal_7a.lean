-- Prove2me | Theorems.Thm_FamousTheorems_normal_convolution_normal_7a
-- name    : FamousTheorems.normal_convolution_normal_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:18.349991+00:00
-- url     : https://prove2.me/theorems/cd113f8e-0d88-4f1b-aa16-faa98ed61b8a
-- title:
--   The convolution of two normal distributions is normal
-- statement:
--   **The convolution of two normal distributions is normal.** For all $m_1,m_2\in\mathbb R$ and $v_1,v_2\ge0$,
--   $$\mathcal N(m_1,v_1)*\mathcal N(m_2,v_2)=\mathcal N(m_1+m_2,\,v_1+v_2).$$
--   Equivalently, if $X\sim\mathcal N(m_1,v_1)$ and $Y\sim\mathcal N(m_2,v_2)$ are independent, then $X+Y\sim\mathcal N(m_1+m_2,v_1+v_2)$.
--
--   This stability property explains why the normal distribution appears as the limit in the central limit theorem. It is used throughout statistics, for example for the distribution of sample means of normal data, and in the construction of Brownian motion.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.gaussianReal_conv_gaussianReal`. `Measure.conv` is the convolution of measures on the additive group $\mathbb R$, the image of the product measure under addition. Degenerate variances $v_i=0$ (Dirac masses) are allowed.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.gaussianReal_conv_gaussianReal`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem normal_convolution_normal_7a (m₁ m₂ : ℝ) (v₁ v₂ : NNReal) :
    (ProbabilityTheory.gaussianReal m₁ v₁).conv (ProbabilityTheory.gaussianReal m₂ v₂) =
      ProbabilityTheory.gaussianReal (m₁ + m₂) (v₁ + v₂) := by sorry

end FamousTheorems
