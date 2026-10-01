-- Prove2me | Theorems.Thm_FoundationsML_ModelSelection_cv_vs_srm
-- name    : FoundationsML.ModelSelection.cv_vs_srm
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:23:55.128362+00:00
-- url     : https://prove2.me/theorems/1931ec0f-25e9-491b-8ac0-662ca6d33518
-- title:
--   Theorem 4.4 — Cross-validation versus SRM
-- statement:
--   **Statement (Theorem 4.4, p. 69, PDF p. 86).** Split a sample of size $m$ into a training
--   sample $S_1$ of size $(1-\alpha)m$ and a validation sample $S_2$ of size $\alpha m$, and let
--   $(H_k)_{k\ge1}$ be a nested family. Let $h_S^{CV}$ be the cross-validation hypothesis: among
--   the per-$k$ ERM solutions on $S_1$, the one with least empirical error on $S_2$ (Eq. 4.7).
--   Let $h_{S_1}^{SRM}$ be the SRM hypothesis trained on $S_1$ alone, minimizing empirical error
--   plus complexity penalty over the same family. Then for any $\delta>0$, with probability at
--   least $1-\delta$:
--   $$R(h_S^{CV}) - R(h_{S_1}^{SRM}) \le
--   2\sqrt{\tfrac{\log\max(k(h_S^{CV}),k(h_{S_1}^{SRM}))}{\alpha m}} +
--   2\sqrt{\tfrac{\log(4/\delta)}{2\alpha m}}.$$
--   This compares the two model-selection procedures directly, showing CV's guarantee for a
--   sample of size $m$ tracks SRM's guarantee for the smaller training sample of size
--   $(1-\alpha)m$.
--
--   **Formalization Note.** `S1 : Fin m1 → X`, `S2 : Fin m2 → X` are two genuinely distinct
--   samples (per `BRIEF.md`'s pitfall note); `hm1`/`hm2` pin `m1=(1-\alpha)m`, `m2=\alpha m`
--   exactly; `hCV`/`hSRM1` are two distinct hypothesis-valued functions of the samples, matching
--   "two different model-selection procedures on two different samples," never conflated. The
--   probability is over the product measure on `(S1, S2)`. **Revision (2026-09-19).**
--   `hCV`/`hSRM1` originally carried only a set-membership hypothesis (`∈ Hk k` for *some* `k`),
--   which let them be arbitrary functions unconnected to the book's actual ERM/SRM-minimizing
--   definitions — the moderator found a concrete counterexample making the drafted inequality
--   false. Fixed by pinning `hCV S1 S2` to an actual per-$k$ ERM solution
--   (`hERMk`/`hERMk_mem`/`hERMk_min`) with least empirical error on `S2` among all of them
--   (`hCV_eq`, `hCV_min` — Eq. 4.7 exactly), by giving `hSRM1` the same minimization property
--   `srm_learning_guarantee`'s `hSRM_min` states (`hSRM1_min`), and by adding the nestedness
--   hypothesis `hNested` Theorem 4.2's proof (invoked on `S1`) requires. Also specialized `Y`
--   from a generic type to `ℝ`, matching `srm_learning_guarantee`'s own setting: the added
--   `hSRM1_min` hypothesis needs `RademacherComplexity`, which this chunk's restatement of
--   Definitions 3.1/3.2 only defines for real-valued hypothesis families.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 69, Theorem 4.4 (PDF p. 86)

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError
import Definitions.Def_FoundationsML_ModelSelection_RademacherComplexity
import Definitions.Def_FoundationsML_ModelSelection_LeastIndex

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- Theorem 4.4 (Cross-validation versus SRM; Mohri, Rostamizadeh & Talwalkar, *Foundations
of Machine Learning*, 2nd ed., MIT Press 2018, p. 69, PDF p. 86). A sample of size `m` is
split into a training sample `S1` of size `m1` and a validation sample `S2` of size `m2`, with
`m1 = (1 − α)m` and `m2 = αm`. `(H_k)_{k≥1}` is a nested family (`hNested`). `hERMk S1 k` is the
ERM solution on `S1` within `H_k` (`hERMk_mem`, `hERMk_min`); `hCV S1 S2` is the cross-validation
hypothesis (Eq. 4.7): some `hERMk S1 k` (`hCV_eq`) with least empirical error on `S2` among all
of them (`hCV_min`). `hSRM1 S1` is the SRM hypothesis trained on `S1` alone (`hSRM1_min`, the
same minimization property as `srm_learning_guarantee`'s `hSRM_min`), using the same nested
family. Then for any `δ > 0`, with probability at least `1 − δ` over the draw of `(S1, S2)`,
`R(h_S^CV) − R(h_{S1}^SRM) ≤ 2 sqrt(log max(k(h_S^CV), k(h_{S1}^SRM)) / (αm)) +
2 sqrt(log(4/δ) / (2αm))`. -/
theorem cv_vs_srm {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c : X → ℝ) (Hk : ℕ → Set (X → ℝ)) (m m1 m2 : ℕ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hm1 : (m1 : ℝ) = (1 - α) * m) (hm2 : (m2 : ℝ) = α * m)
    (hNested : ∀ k, 1 ≤ k → Hk k ⊆ Hk (k + 1))
    (hCV : (Fin m1 → X) → (Fin m2 → X) → (X → ℝ))
    (hSRM1 : (Fin m1 → X) → (X → ℝ))
    (hERMk : (Fin m1 → X) → ℕ → (X → ℝ))
    (hERMk_mem : ∀ S1 k, 1 ≤ k → hERMk S1 k ∈ Hk k)
    (hERMk_min : ∀ S1 k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S1 c (hERMk S1 k) ≤ EmpiricalError S1 c h)
    (hCV_eq : ∀ S1 S2, ∃ k, 1 ≤ k ∧ hCV S1 S2 = hERMk S1 k)
    (hCV_min : ∀ S1 S2, ∀ k, 1 ≤ k → EmpiricalError S2 c (hCV S1 S2) ≤ EmpiricalError S2 c (hERMk S1 k))
    (hCV_mem : ∀ S1 S2, ∃ k, 1 ≤ k ∧ hCV S1 S2 ∈ Hk k)
    (hSRM1_mem : ∀ S1, ∃ k, 1 ≤ k ∧ hSRM1 S1 ∈ Hk k)
    (hSRM1_min : ∀ S1, ∀ k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S1 c (hSRM1 S1) + RademacherComplexity D (Hk (LeastIndex Hk (hSRM1 S1))) m1 +
          Real.sqrt (Real.log (LeastIndex Hk (hSRM1 S1)) / m1) ≤
        EmpiricalError S1 c h + RademacherComplexity D (Hk k) m1 + Real.sqrt (Real.log k / m1))
    (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.prod (Measure.pi (fun _ : Fin m1 => D)) (Measure.pi (fun _ : Fin m2 => D))
      {p : (Fin m1 → X) × (Fin m2 → X) |
        GeneralizationError D c (hCV p.1 p.2) - GeneralizationError D c (hSRM1 p.1) ≤
          2 * Real.sqrt (Real.log
              (max (LeastIndex Hk (hCV p.1 p.2)) (LeastIndex Hk (hSRM1 p.1))) / (α * m)) +
          2 * Real.sqrt (Real.log (4 / δ) / (2 * α * m))}).toReal := by sorry

end FoundationsML.ModelSelection
