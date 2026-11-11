-- Prove2me | Theorems.Thm_DataDepProb_Discrete_fact_4_7
-- name    : DataDepProb.Discrete.fact_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:10:36.972229+00:00
-- url     : https://prove2.me/theorems/876848df-7d38-40c5-97a8-b9fb1d80096f
-- title:
--   Fact 4.7 — empirical fourth moment $E\|\hat D_S-D\|_2^4\le3/m^2$
-- statement:
--   For $D\in\Delta_d$, $m\ge1$ and $S\sim D^m$,
--   $$E\|\hat D_S-D\|_2^4\le\frac3{m^2}.$$
--   This fourth-moment bound controls the expected squared penalty $E\,P_S(\tilde D)$ in Lemma 6.2.
--
--   Differences from the source:
--   - encoding: $E$ over $S\sim D^m$ and $\|\cdot\|_2^4$ → the finite sum $\sum_s D^m(s)\big(\sum_x(\hat D_s(x)-D(x))^2\big)^2$ over $s:$ `Fin m → Fin d`; reason: the same expectation on a finite space.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 9, Fact 4.7 (proof p. 28, §A.2)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex

namespace DataDepProb.Discrete

/-- Fact 4.7 (empirical fourth moment, p. 9). For `D ∈ ∆_d`, `m ≥ 1` and `S ∼ D^m`,
`E‖D̂_S − D‖₂⁴ ≤ 3/m²`; the expectation is the finite sum over samples `s ∈ [d]^m` weighted by
`D^m(s) = ∏_i D(s_i)`. -/
theorem fact_4_7 {m d : ℕ} (hm : 1 ≤ m) (D : Fin d → ℝ) (hD : D ∈ simplex d) :
    ∑ s : Fin m → Fin d, sampleProb D s * (∑ x, (empirical s x - D x) ^ 2) ^ 2
      ≤ 3 / (m : ℝ) ^ 2 := by sorry

end DataDepProb.Discrete
