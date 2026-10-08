-- Prove2me | Theorems.Thm_FoundationsML_ModelSelection_srm_learning_guarantee_v2
-- name    : FoundationsML.ModelSelection.srm_learning_guarantee_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:13.138529+00:00
-- url     : https://prove2.me/theorems/59b3d600-59c8-42a2-820a-855a7c11b29e
-- title:
--   Theorem 4.2 — SRM learning guarantee (goal; binary hypotheses, $m\ge1$)
-- statement:
--   **Statement (Theorem 4.2, p. 66, PDF p. 83).** Let $H=\bigcup_{k\ge1}H_k$ be a nested countable union of hypothesis sets of $\{-1,+1\}$-valued (measurable) functions, $c$ a $\{-1,+1\}$-valued target, and for $h\in H$ let $k(h)$ be the least index with $h\in H_{k(h)}$. Let $h_S^{SRM}$ minimize $F_k(h)=\hat R_S(h)+R_m(H_k)+\sqrt{\log k/m}$ over $k\ge1,\,h\in H_k$. Then for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample $S$ of size $m\ge1$ from $D^m$:
--   $$R(h_S^{SRM}) \le \inf_{h\in H}\Big[R(h) + 2R_m(H_{k(h)}) + \sqrt{\tfrac{\log k(h)}m}\Big] + \sqrt{\tfrac{2\log(3/\delta)}m}.$$
--
--   **Formalization Note.** The retired version allowed $m=0$, where every sample-dependent term is Lean's $x/0=0$, the SRM minimization hypothesis becomes vacuous and the bound is false. Changes: (i) $m\ge1$, $\delta\in(0,1)$ (standing conventions); (ii) hypotheses and target take values in $\{-1,+1\}$ — Chapter 4's binary-classification setting, in which the penalty $R_m(H_k)$ with coefficient $1$ in $F_k$ (Theorem 3.5 via Lemma 3.4) is valid; for arbitrary real-valued $h$ compared through $h(x)\neq c(x)$ the statement is false (a class of tiny-scale functions has tiny $R_m$ but can fit any sample); (iii) the book's standing measurability of $c$ and of every $h\in H_k$ (footnote 2, p. 10) and of the supremum defining $\hat R_S(H_k)$ (footnote 3, p. 30; needed for $R_m(H_k)$ to be the book's expectation rather than Lean's junk $0$) are explicit; (iv) the corrected `RademacherComplexity` (`_v2`, supremum over exactly $H_k$) is used. As before: the deterministic scenario (target concept $c$, the special case of §2.4.1) is used, consistent with the mission's definition layer; nestedness is §4.3's standing assumption; `hSRM_min` is the literal argmin property of $h_S^{SRM}$; `hHne` keeps the outer infimum over a nonempty set (its image is bounded below by $0$).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 66, Theorem 4.2 (PDF p. 83)

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError
import Definitions.Def_FoundationsML_ModelSelection_RademacherComplexity_v2
import Definitions.Def_FoundationsML_ModelSelection_LeastIndex

open MeasureTheory

namespace FoundationsML.ModelSelection

/-- Theorem 4.2 (SRM learning guarantee; goal; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 66, PDF p. 83). Let
`(H_k)_{k≥1}` be a nested countable family of hypothesis sets of `{−1,+1}`-valued functions
(§4.3's standing assumptions), `H = ⋃_{k≥1} H_k`, and for `h ∈ H` let `k(h) = LeastIndex Hk h`
be the least index with `h ∈ H_{k(h)}`. Let `hSRM S` minimize
`F_k(h) = R̂_S(h) + R_m(H_k) + sqrt(log k / m)` over `k ≥ 1, h ∈ H_k` (`hSRM_min`). Then for
any `δ > 0`, with probability at least `1 − δ` over the draw of an i.i.d. sample `S` of size
`m ≥ 1` from `D^m`,
`R(h_S^SRM) ≤ inf_{h∈H} [R(h) + 2 R_m(H_{k(h)}) + sqrt(log k(h)/m)] + sqrt(2 log(3/δ)/m)`.

**Formalization Note.** Replaces `srm_learning_guarantee`, which allowed `m = 0` (every
sample-dependent term is then Lean's `x / 0 = 0`, `hSRM_min` becomes vacuous and the bound
false). Changes: `m ≥ 1`, `δ ∈ (0,1)` (standing conventions); the hypotheses in `H_k` and the
target `c` take values in `{−1,+1}` (Chapter 4's binary-classification setting, in which the
penalty `R_m(H_k)` with coefficient `1` in `F_k`, i.e. Theorem 3.5 via Lemma 3.4, is valid;
for real-valued `h` compared through `h(x) ≠ c(x)` the statement is false); the book's
standing measurability of `c` and of every `h ∈ H_k` (footnote 2, p. 10) and of the supremum
defining `R̂_S(H_k)` (footnote 3, p. 30, `hHk_sup`, needed for `R_m(H_k)` to be the book's
expectation rather than Lean's junk `0`) are explicit; `RademacherComplexity` is the corrected
`_v2` version (supremum over exactly `H_k`). As in the retired version, the deterministic
scenario (target concept `c`, §2.4.1's special case of the stochastic one) is used, `hNested`
is §4.3's standing assumption, `hSRM_min` is the literal argmin property of `h_S^SRM` and
`hHne` keeps the outer `inf` over a nonempty set (its image is bounded below by `0`). -/
theorem srm_learning_guarantee_v2 {X : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] (c : X → ℝ) (hc : ∀ x, c x = 1 ∨ c x = -1)
    (hc_meas : Measurable c) (Hk : ℕ → Set (X → ℝ))
    (hHk : ∀ k, 1 ≤ k → ∀ h ∈ Hk k, ∀ x, h x = 1 ∨ h x = -1)
    (hHk_meas : ∀ k, 1 ≤ k → ∀ h ∈ Hk k, Measurable h)
    (hNested : ∀ k, 1 ≤ k → Hk k ⊆ Hk (k + 1))
    (m : ℕ) (hm : 0 < m)
    (hHk_sup : ∀ k, 1 ≤ k →
      Measurable (fun S : Fin m → X => EmpiricalRademacherComplexity (Hk k) S))
    (hSRM : (Fin m → X) → (X → ℝ))
    (hSRM_mem : ∀ S, ∃ k, 1 ≤ k ∧ hSRM S ∈ Hk k)
    (hSRM_min : ∀ S, ∀ k, 1 ≤ k → ∀ h ∈ Hk k,
      EmpiricalError S c (hSRM S) + RademacherComplexity D (Hk (LeastIndex Hk (hSRM S))) m +
          Real.sqrt (Real.log (LeastIndex Hk (hSRM S)) / m) ≤
        EmpiricalError S c h + RademacherComplexity D (Hk k) m + Real.sqrt (Real.log k / m))
    (hHne : (⋃ k ≥ 1, Hk k).Nonempty)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (hSRM S) ≤
        sInf ((fun h => GeneralizationError D c h +
            2 * RademacherComplexity D (Hk (LeastIndex Hk h)) m +
            Real.sqrt (Real.log (LeastIndex Hk h) / m)) '' (⋃ k ≥ 1, Hk k)) +
        Real.sqrt (2 * Real.log (3 / δ) / m)}).toReal := by sorry

end FoundationsML.ModelSelection
