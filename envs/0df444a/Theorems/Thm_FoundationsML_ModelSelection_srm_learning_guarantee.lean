-- Prove2me | Theorems.Thm_FoundationsML_ModelSelection_srm_learning_guarantee
-- name    : FoundationsML.ModelSelection.srm_learning_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:23:05.467898+00:00
-- url     : https://prove2.me/theorems/efc3b68e-517e-4e8d-be2f-d62a7ec4eedb
-- title:
--   Theorem 4.2 — SRM learning guarantee (goal)
-- statement:
--   **Statement (Theorem 4.2, p. 66, PDF p. 83).** Let $H=\bigcup_{k\ge1}H_k$ be a nested
--   countable union of hypothesis sets, and for $h\in H$ let $k(h)$ be the least index with
--   $h\in H_{k(h)}$. Let $h_S^{SRM}$ minimize $F_k(h)=\hat R_S(h)+R_m(H_k)+\sqrt{\log k/m}$ over
--   $k\ge1,\,h\in H_k$. Then for any $\delta>0$, with probability at least $1-\delta$ over an
--   i.i.d. sample $S$ of size $m$ from $D^m$:
--   $$R(h_S^{SRM}) \le \inf_{h\in H}\Big[R(h) + 2R_m(H_{k(h)}) + \sqrt{\tfrac{\log k(h)}m}\Big]
--   + \sqrt{\tfrac{2\log(3/\delta)}m}.$$
--   This is the chapter's capstone: SRM's guarantee is, up to the extra $\sqrt{\log k(h)/m}$
--   term, as favorable as if an oracle had revealed the best-in-class hypothesis's own index
--   $k(h^*)$ in advance — the balance between fit and complexity SRM's `inf` expresses.
--
--   **Formalization Note.** `Hk : ℕ → Set (X → ℝ)` (real-valued, so `RademacherComplexity`
--   applies directly, matching the book's own unqualified `R_m(H_k)`); `hNested` states
--   $H_k\subseteq H_{k+1}$ explicitly (the book's assumption, per `BRIEF.md`'s pitfall note,
--   is never left implicit here); `hSRM_min` is the literal minimization property defining
--   $h_S^{SRM}$ as an argmin over the whole union, not a restatement for one fixed $k$;
--   `hHne` guards the outer `sInf` against trap 5. The countable union bound with weight
--   `1/k²` inside the book's proof (Eq. 4.5) is genuine content of the *proof*, not the
--   *statement*, so it does not appear in the Lean statement itself, only its constant `3`
--   survives into the `log(3/δ)` term the statement displays.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 66, Theorem 4.2 (PDF p. 83)

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError
import Definitions.Def_FoundationsML_ModelSelection_RademacherComplexity
import Definitions.Def_FoundationsML_ModelSelection_LeastIndex

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- Theorem 4.2 (SRM learning guarantee; Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 66, PDF p. 83). Let `(H_k)_{k≥1}` be a nested
countable family of hypothesis sets (`hNested`), and for `h` in the union `H = ⋃_{k≥1} H_k`
let `k(h) = LeastIndex Hk h` be the least index with `h ∈ H_{k(h)}`. Let `hSRM S` minimize
`F_k(h) = R̂_S(h) + R_m(H_k) + sqrt(log k / m)` over `k ≥ 1, h ∈ H_k` (`hSRM_min`). Then for
any `δ > 0`, with probability at least `1 − δ` over the draw of an i.i.d. sample `S` of size
`m` from `D^m`,
`R(h_S^SRM) ≤ inf_{h∈H} [R(h) + 2 R_m(H_{k(h)}) + sqrt(log k(h)/m)] + sqrt(2 log(3/δ)/m)`. -/
theorem srm_learning_guarantee {X : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] (c : X → ℝ) (Hk : ℕ → Set (X → ℝ))
    (hNested : ∀ k, 1 ≤ k → Hk k ⊆ Hk (k + 1))
    (m : ℕ) (hSRM : (Fin m → X) → (X → ℝ))
    (hSRM_mem : ∀ S, ∃ k, 1 ≤ k ∧ hSRM S ∈ Hk k)
    (hSRM_min : ∀ S, ∀ k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S c (hSRM S) + RademacherComplexity D (Hk (LeastIndex Hk (hSRM S))) m +
          Real.sqrt (Real.log (LeastIndex Hk (hSRM S)) / m) ≤
        EmpiricalError S c h + RademacherComplexity D (Hk k) m + Real.sqrt (Real.log k / m))
    (hHne : (⋃ k ≥ 1, Hk k).Nonempty)
    (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (hSRM S) ≤
        sInf ((fun h => GeneralizationError D c h +
            2 * RademacherComplexity D (Hk (LeastIndex Hk h)) m +
            Real.sqrt (Real.log (LeastIndex Hk h) / m)) '' (⋃ k ≥ 1, Hk k)) +
        Real.sqrt (2 * Real.log (3 / δ) / m)}).toReal := by sorry

end FoundationsML.ModelSelection
