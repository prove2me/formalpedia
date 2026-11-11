-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_4_3
-- name    : DoubleCorrRME.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:04.022211+00:00
-- url     : https://prove2.me/theorems/1d4a7294-e2e6-4937-a84c-2798d64d94b9
-- title:
--   Lemma 4.3 ([PP25, Thm 22]), p.21 — a stable subset of $1-\alpha'$ of the samples exists w.p. $1-q$
-- statement:
--   Let $Z_1,\dots,Z_m$ be i.i.d. samples from a law $P$ on $\mathbb R^d$ with mean $\mu$ and covariance $\Sigma\preceq I_d$, and let $q\in(0,1)$. There are universal constants $c,C_\alpha,C_\Delta>0$ such that the following holds. Let $\eta\in(0,c)$,
--
--   $$\alpha'=C_\alpha\Big(\eta+\frac{\log(1/q)}m\Big)\le c,\qquad \Delta=C_\Delta\Big(\sqrt{\frac{\operatorname{tr}\Sigma}m}+\sqrt{\alpha'}+\sqrt{\frac{\log(1/q)}m}\Big).$$
--
--   Then with probability at least $1-q$ there is an index set $\mathcal I\subseteq[m]$ with $|\mathcal I|\ge(1-\alpha')m$ such that $\{Z_k:k\in\mathcal I\}$ is $(\alpha',\Delta)$-stable with respect to $(\mu,I_d)$.
--
--   This is the first stable reference (Lemma 4.1, Part 1) with the sub-Gaussian dependence on $\log(1/q)$.
--
--   **Formalization Note** "With probability at least $1-q$ there is" means: a measurable set of samples of probability at least $1-q$ on each of which such an $\mathcal I$ exists.
--
--   Differences from the source:
--   - encoding: m = Nn → any sample size m ≥ 1; reason: m = Nn is only a name in the lemma; every m ≥ 1 is of that form (N = m, n = 1)
--   - encoding: α′ = O(η + log(1/q)/m), ∆ := O(…), "sufficiently small universal constant c" → ∃ c, C_α, C_∆ > 0 before m, d, P, q, η; α′, ∆ defined with them; reason: meaning of the O(·) constants
--   - reading: "with probability at least 1 − q, there exists an index set ℐ" → a measurable set of samples of P^{⊗m}-probability ≥ 1 − q on which ℐ exists; reason: avoids the probability of a possibly non-measurable event; it implies the inner-probability reading
--   - encoding: mean µ and covariance Σ ⪯ I_d → IsBoundedCovLaw P (MemLp id 2, E⟨u, x − µ⟩² ≤ ∥u∥²), tr Σ = E∥x − µ∥²; reason: the mean and covariance exist exactly under a finite second moment
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 4.3, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Stability

open MeasureTheory

namespace DoubleCorrRME

/-- **Lemma 4.3** ([PP25, Theorem 22]), p.21 (PDF p.22).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Let m = Nn, q ∈ (0, 1), and Z_1, …, Z_m ∈ ℝ^d be i.i.d. samples from a distribution P over ℝ^d with
mean µ and covariance Σ ⪯ I_d. Let η ∈ (0, c) and α′ = O(η + log(1/q)/m) ≤ c for a sufficiently
small universal constant c > 0, and let ∆ := O(√(tr[Σ]/m) + √α′ + √(log(1/q)/m)). Then, with
probability at least 1 − q, there exists an index set ℐ ⊆ [m] such that |ℐ| ≥ (1 − α′)m and the
multiset S_ℐ := {z_k : k ∈ ℐ} is (α′, ∆)-stable with respect to (µ, I_d)."

**Formalization Note.**
* The constants `c`, `C_α` (of `α′`) and `C_∆` (of `∆`) are chosen before `m, d, P, q, η`;
  `α′ := C_α(η + log(1/q)/m)`, `∆ := C_∆(√(tr Σ/m) + √α′ + √(log(1/q)/m))` with
  `tr Σ = E‖x − µ‖²`.
* `m ≥ 1` is any sample size: `m = Nn` is only a name here.
* "With probability at least `1 − q`, there exists `ℐ`": a measurable set of samples of
  `P^{⊗m}`-probability at least `1 − q` on which such an `ℐ` exists.
* `P` has finite second moment and `Σ ⪯ I_d` (`IsBoundedCovLaw`). -/
theorem lemma_4_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ Cα : ℝ, 0 < Cα ∧ ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ (m d : ℕ), 1 ≤ m → ∀ (P : Measure (Vec d)) [IsProbabilityMeasure P], IsBoundedCovLaw P →
        ∀ q η : ℝ, 0 < q → q < 1 → 0 < η → η < c →
          let α' : ℝ := Cα * (η + Real.log (1 / q) / m)
          let Δ : ℝ := CΔ * (Real.sqrt ((∫ x, ‖x - popMean P‖ ^ 2 ∂P) / m) + Real.sqrt α' +
            Real.sqrt (Real.log (1 / q) / m))
          α' ≤ c →
          ∃ S : Set (Fin m → Vec d), MeasurableSet S ∧
            ENNReal.ofReal (1 - q) ≤ (Measure.pi fun _ : Fin m => P) S ∧
            ∀ Z ∈ S, ∃ I : Finset (Fin m), (1 - α') * (m : ℝ) ≤ I.card ∧
              IsStable Z I α' Δ (popMean P) 1 := by sorry

end DoubleCorrRME
