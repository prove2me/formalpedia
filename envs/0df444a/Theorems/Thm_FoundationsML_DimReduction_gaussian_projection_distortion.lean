-- Prove2me | Theorems.Thm_FoundationsML_DimReduction_gaussian_projection_distortion
-- name    : FoundationsML.DimReduction.gaussian_projection_distortion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:29:13.375224+00:00
-- url     : https://prove2.me/theorems/04ee5016-6b69-4c87-bc04-9ea57607c877
-- title:
--   Lemma 15.3 — Gaussian random projection distortion bound (milestone)
-- statement:
--   **Statement (Lemma 15.3, p. 355, PDF p. 372).** Let $x\in\mathbb R^N$, define $k<N$ and
--   assume that entries in $A\in\mathbb R^{k\times N}$ are sampled independently from the
--   standard normal distribution $N(0,1)$. Then, for any $0<\epsilon<1/2$,
--   $$P\Big[(1-\epsilon)\|x\|^2 \le \Big\|\tfrac1{\sqrt k}Ax\Big\|^2 \le (1+\epsilon)\|x\|^2\Big]
--   \ge 1-2e^{-(\epsilon^2-\epsilon^3)k/4}.$$
--
--   This is the single-pair (single fixed vector $x=u-v$) distortion-probability bound that
--   Lemma 15.4's union bound over $O(m^2)$ pairs is built from, obtained by recognizing that
--   $\|\tfrac1{\sqrt k}Ax\|^2/\|x\|^2$ has exactly a $\chi^2_k$ distribution and applying
--   Lemma 15.2.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 355, Lemma 15.3 (PDF p. 372)

import Mathlib
import Definitions.Def_FoundationsML_DimReduction_IsIIDStandardGaussianMatrix
import Definitions.Def_FoundationsML_DimReduction_SqNorm

open MeasureTheory

namespace FoundationsML.DimReduction

/-- Lemma 15.3 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 355, PDF p. 372). Let `x ∈ ℝ^N`, define `k < N` and assume that entries in
`A ∈ ℝ^{k×N}` are sampled independently from the standard normal distribution `N(0,1)`. Then,
for any `0 < ε < 1/2`,
`P[(1−ε)‖x‖² ≤ ‖(1/√k)Ax‖² ≤ (1+ε)‖x‖²] ≥ 1 − 2exp(−(ε²−ε³)k/4)`. -/
theorem gaussian_projection_distortion {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob] {N k : ℕ} (hk : k < N)
    (A : Ω → Matrix (Fin k) (Fin N) ℝ) (hA : IsIIDStandardGaussianMatrix Prob A)
    (x : Fin N → ℝ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    1 - 2 * Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) ≤
      Prob.real {ω | (1 - ε) * SqNorm x ≤
          SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ∧
        SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ≤ (1 + ε) * SqNorm x} := by sorry

end FoundationsML.DimReduction
