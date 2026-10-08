-- Prove2me | Theorems.Thm_FoundationsML_ModelSelection_cv_vs_srm_v2
-- name    : FoundationsML.ModelSelection.cv_vs_srm_v2
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:14.666963+00:00
-- url     : https://prove2.me/theorems/d88da1af-f52a-44cc-8342-27b7daeff163
-- title:
--   Theorem 4.4 — cross-validation versus SRM (binary hypotheses, $m\ge1$)
-- statement:
--   **Statement (Theorem 4.4, p. 69, PDF p. 86).** Split a sample of size $m\ge1$ into a training sample $S_1$ of size $(1-\alpha)m$ and a validation sample $S_2$ of size $\alpha m$, $0<\alpha<1$, and let $(H_k)_{k\ge1}$ be a nested family of $\{-1,+1\}$-valued (measurable) hypothesis sets with a $\{-1,+1\}$-valued target $c$. Let $h_S^{CV}$ be the cross-validation hypothesis: among the per-$k$ ERM solutions on $S_1$, one with least empirical error on $S_2$ (Eq. 4.7). Let $h_{S_1}^{SRM}$ be the SRM hypothesis trained on $S_1$ alone. Then for any $\delta\in(0,1)$, with probability at least $1-\delta$:
--   $$R(h_S^{CV}) - R(h_{S_1}^{SRM}) \le 2\sqrt{\tfrac{\log\max(k(h_S^{CV}),k(h_{S_1}^{SRM}))}{\alpha m}} + 2\sqrt{\tfrac{\log(4/\delta)}{2\alpha m}}.$$
--
--   **Formalization Note.** The retired version allowed $m=m_1=m_2=0$, where every sample-dependent term is Lean's $x/0=0$, all minimality hypotheses become vacuous and the bound is false. Changes: $m\ge1$ (with $0<\alpha<1$ and $m_2=\alpha m\in\mathbb N$ this forces $m_1,m_2\ge1$), $\delta\in(0,1)$; hypotheses and target $\{-1,+1\}$-valued (Chapter 4's binary setting, required by Theorem 4.2 which the proof invokes on $S_1$); the book's standing measurability of $c$, of every $h\in H_k$ (footnote 2, p. 10) and of the supremum defining $\hat R_{S_1}(H_k)$ (footnote 3, p. 30) explicit; the corrected `RademacherComplexity` (`_v2`). As before, $S_1$ and $S_2$ are two distinct samples with the product measure, and the selectors are pinned by their literal minimization properties (Eq. 4.7 for CV, Theorem 4.2's argmin for SRM).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 69, Theorem 4.4 (PDF p. 86)

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError
import Definitions.Def_FoundationsML_ModelSelection_RademacherComplexity_v2
import Definitions.Def_FoundationsML_ModelSelection_LeastIndex

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- Theorem 4.4 (Cross-validation versus SRM; Mohri, Rostamizadeh & Talwalkar, *Foundations
of Machine Learning*, 2nd ed., MIT Press 2018, p. 69, PDF p. 86). A sample of size `m ≥ 1` is
split into a training sample `S1` of size `m1 = (1 − α)m` and a validation sample `S2` of size
`m2 = αm`, `0 < α < 1`. `(H_k)_{k≥1}` is a nested family of `{−1,+1}`-valued hypothesis sets.
`hERMk S1 k` is the ERM solution on `S1` within `H_k`; `hCV S1 S2` is the cross-validation
hypothesis (Eq. 4.7): some `hERMk S1 k` with least empirical error on `S2` among all of them;
`hSRM1 S1` is the SRM hypothesis trained on `S1` alone. Then for any `δ > 0`, with probability
at least `1 − δ` over the draw of `(S1, S2)`,
`R(h_S^CV) − R(h_{S1}^SRM) ≤ 2 sqrt(log max(k(h_S^CV), k(h_{S1}^SRM)) / (αm)) +
2 sqrt(log(4/δ) / (2αm))`.

**Formalization Note.** Replaces `cv_vs_srm`, which allowed `m = m1 = m2 = 0` (every
sample-dependent term is then Lean's `x / 0 = 0`, all minimality hypotheses become vacuous and
the bound false). Changes: `m ≥ 1` (with `0 < α < 1` and `m2 = αm ∈ ℕ` this forces
`m1, m2 ≥ 1`), `δ ∈ (0,1)`; the hypotheses in `H_k` and the target `c` are `{−1,+1}`-valued
(Chapter 4's binary setting, required by Theorem 4.2 which this proof invokes on `S1`); the
book's standing measurability of `c`, of every `h ∈ H_k` (footnote 2, p. 10) and of the
supremum defining `R̂_{S1}(H_k)` (footnote 3, p. 30, `hHk_sup`) are explicit;
`RademacherComplexity` is the corrected `_v2` version. The selectors `hERMk`, `hCV`, `hSRM1`
are pinned by their literal minimization properties as in the retired version. -/
theorem cv_vs_srm_v2 {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c : X → ℝ) (hc : ∀ x, c x = 1 ∨ c x = -1) (hc_meas : Measurable c)
    (Hk : ℕ → Set (X → ℝ))
    (hHk : ∀ k, 1 ≤ k → ∀ h ∈ Hk k, ∀ x, h x = 1 ∨ h x = -1)
    (hHk_meas : ∀ k, 1 ≤ k → ∀ h ∈ Hk k, Measurable h)
    (m m1 m2 : ℕ) (hm : 0 < m) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hm1 : (m1 : ℝ) = (1 - α) * m) (hm2 : (m2 : ℝ) = α * m)
    (hNested : ∀ k, 1 ≤ k → Hk k ⊆ Hk (k + 1))
    (hHk_sup : ∀ k, 1 ≤ k →
      Measurable (fun S : Fin m1 → X => EmpiricalRademacherComplexity (Hk k) S))
    (hCV : (Fin m1 → X) → (Fin m2 → X) → (X → ℝ))
    (hSRM1 : (Fin m1 → X) → (X → ℝ))
    (hERMk : (Fin m1 → X) → ℕ → (X → ℝ))
    (hERMk_mem : ∀ S1 k, 1 ≤ k → hERMk S1 k ∈ Hk k)
    (hERMk_min : ∀ S1 k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S1 c (hERMk S1 k) ≤ EmpiricalError S1 c h)
    (hCV_eq : ∀ S1 S2, ∃ k, 1 ≤ k ∧ hCV S1 S2 = hERMk S1 k)
    (hCV_min : ∀ S1 S2, ∀ k, 1 ≤ k →
      EmpiricalError S2 c (hCV S1 S2) ≤ EmpiricalError S2 c (hERMk S1 k))
    (hCV_mem : ∀ S1 S2, ∃ k, 1 ≤ k ∧ hCV S1 S2 ∈ Hk k)
    (hSRM1_mem : ∀ S1, ∃ k, 1 ≤ k ∧ hSRM1 S1 ∈ Hk k)
    (hSRM1_min : ∀ S1, ∀ k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S1 c (hSRM1 S1) +
          RademacherComplexity D (Hk (LeastIndex Hk (hSRM1 S1))) m1 +
          Real.sqrt (Real.log (LeastIndex Hk (hSRM1 S1)) / m1) ≤
        EmpiricalError S1 c h + RademacherComplexity D (Hk k) m1 + Real.sqrt (Real.log k / m1))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.prod (Measure.pi (fun _ : Fin m1 => D)) (Measure.pi (fun _ : Fin m2 => D))
      {p : (Fin m1 → X) × (Fin m2 → X) |
        GeneralizationError D c (hCV p.1 p.2) - GeneralizationError D c (hSRM1 p.1) ≤
          2 * Real.sqrt (Real.log
              (max (LeastIndex Hk (hCV p.1 p.2)) (LeastIndex Hk (hSRM1 p.1))) / (α * m)) +
          2 * Real.sqrt (Real.log (4 / δ) / (2 * α * m))}).toReal := by sorry

end FoundationsML.ModelSelection
