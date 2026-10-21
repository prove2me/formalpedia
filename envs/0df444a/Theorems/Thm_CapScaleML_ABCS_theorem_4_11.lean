-- Prove2me | Theorems.Thm_CapScaleML_ABCS_theorem_4_11
-- name    : CapScaleML.ABCS.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:34.874176+00:00
-- url     : https://prove2.me/theorems/29617f40-1f40-4a54-b316-fcd9570de8fa
-- title:
--   Theorem 4.11 — adaptive ABCS competitive ratio
-- statement:
--   Fix positive waiting and activation prices $\omega,\beta$, nonnegative operating rate $\theta$, horizon $T>0$, and ABCS rates $0<r_1\le R_1$ and $0<r_2\le R_2$. For every nonnegative integrable arrival process $\lambda$, $\eta$-accurate prediction $\tilde\lambda$ with $\eta>0$, AP advice, and ABCS trajectory $m$ driven by that advice,
--   $$
--   \operatorname{Cost}^{\lambda}(m,T)
--   \leq\min\{[1+(\sqrt{2\omega\beta}+\theta)\eta]\,\mathrm{OCR},
--   \mathrm{PCR}\}\operatorname{Opt}.
--   $$
--   OCR and PCR, including constants $c_1$ through $c_6$, are precisely those of equation (4.14). This is the universal cost form of the paper's competitive-ratio bound.
--
--   **Formalization Note** Positive $r_1,r_2$ exclude the source's zero-rate regime, where coefficients become infinite; Lean real division would otherwise return zero. Workload and ABCS are integrated trajectory predicates, and costs use extended nonnegative reals.
-- source:
--   Rutten & Mukherjee, Online Capacity Scaling Augmented With Unreliable Machine Learning Predictions, arXiv:2101.12160v2, p. 16, Theorem 4.11, (4.13)–(4.14)

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS

/-- Theorem 4.11: ABCS is simultaneously OCR-consistent and PCR-robust. -/
theorem theorem_4_11 (ω β θ T r₁ r₂ R₁ R₂ η : ℝ)
    (hω : 0 < ω) (hβ : 0 < β) (hθ : 0 ≤ θ) (hT : 0 < T)
    (hr₁ : 0 < r₁) (hR₁ : r₁ ≤ R₁) (hr₂ : 0 < r₂) (hR₂ : r₂ ≤ R₂)
    (hη : 0 < η) (lam lamHat : ℝ → ℝ)
    (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamHat : ∀ t ∈ Icc 0 T, 0 ≤ lamHat t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T)
    (hacc : IsEtaAccurate ω β θ T η lam lamHat)
    (mAdv qAdv : ℝ → ℝ) (hAP : IsAPAdvice ω β θ T lam lamHat mAdv)
    (hqAdv : IsWorkload T lam mAdv qAdv) (m q : ℝ → ℝ)
    (hm : IsABCS ω β θ T r₁ r₂ R₁ R₂ lam mAdv qAdv m q) :
    cost ω β θ T m q ≤
      min (ENNReal.ofReal ((1 + (Real.sqrt (2 * ω * β) + θ) * η) *
            OCR r₁ r₂ R₁ R₂) * opt ω β θ T lam)
          (ENNReal.ofReal (PCR r₁ r₂ R₁ R₂) * opt ω β θ T lam) := by sorry

end CapScaleML.ABCS
