-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_lemma_5_1
-- name    : ConvexRMDP.Supplement.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:57:14.263991+00:00
-- url     : https://prove2.me/theorems/7991b5df-77f4-4a0b-9320-8a23fada756e
-- title:
--   Lemma 5.1 (Rockafellar, Thm 16.4) — $(\sum_i f_i)^*(y)=\inf\{\sum_i f_i^*(y_i) \mid \sum_i y_i=y\}$
-- statement:
--   Let $f_1, \dots, f_m : \mathbb R^{\mathcal S} \to \mathbb R \cup \{+\infty\}$ be proper closed convex functions such that
--
--   $$
--   \bigcap_{i=1}^m \operatorname{relint}(\operatorname{dom}(f_i)) \neq \emptyset .
--   $$
--
--   Then for every $y \in \mathbb R^{\mathcal S}$,
--
--   $$
--   \Big(\sum_{i=1}^m f_i\Big)^{\!*}(y) = \inf\Big\{ \sum_{i=1}^m f_i^*(y_i) \;\Big|\; y_1, \dots, y_m \in \mathbb R^{\mathcal S},\ \sum_{i=1}^m y_i = y \Big\} .
--   $$
--
--   The conjugate of a sum is the infimal convolution of the conjugates. The paper uses this to compute the conjugate of $f + \xi^\top g_{sa}$ in the proof of Proposition 5.1 and of $\xi_s^\top g_s$ in Theorem 6.2.
--
--   **Formalization Note** Functions are `EReal`-valued; "proper closed convex" is `IsProperClosedConvex`, the relative interior is `intrinsicInterior`, and the infimum is taken in the extended reals (attainment is not claimed, as on the page). The index set $\mathcal S$ is any finite type.
--
--   Differences from the source:
--   - encoding: functions into $\mathbb R \cup \{+\infty\}$ and the infimum → `EReal`-valued functions (properness excludes $-\infty$) and an `EReal` infimum; reason: Lean convention, same instances.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Lemma 5.1, p.17 (citing Rockafellar 1970, Theorem 16.4)

import Mathlib
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_ConvexRMDP_Supplement_conj
import Definitions.Def_TensorAHPE_IsProperClosedConvex

namespace ConvexRMDP

namespace Supplement

/-- **Lemma 5.1 (Theorem 16.4, Rockafellar (1970))** (Grand-Clément & Petrik, arXiv:2209.10187v2,
p.17). Let `f₁, …, f_m : ℝ^S → ℝ ∪ {+∞}` be proper closed convex functions such that
`⋂_{i=1}^m relint(dom(f_i)) ≠ ∅`. Then
`(∑_{i=1}^m f_i)*(y) = inf {∑_{i=1}^m f_i*(y_i) | y₁, …, y_m ∈ ℝ^S, ∑_{i=1}^m y_i = y}` for all `y ∈ ℝ^S`.

**Formalization Note.** Functions into `ℝ ∪ {+∞}` are `EReal`-valued; proper closed convex is
`IsProperClosedConvex`; `relint` is `intrinsicInterior`; the conjugate is `conj`, a supremum over all
of `ℝ^S`. The infimum is taken in `EReal` (as printed: no attainment is claimed). `S` is any finite
index type. -/
theorem lemma_5_1 {S : Type*} [Fintype S] (m : ℕ) (f : Fin m → (S → ℝ) → EReal)
    (hf : ∀ i, TensorAHPE.IsProperClosedConvex (f i))
    (hdom : ∃ p : S → ℝ, ∀ i, p ∈ intrinsicInterior ℝ (AubinLipschitz.effDom (f i)))
    (y : S → ℝ) :
    conj (fun p => ∑ i, f i p) y =
      ⨅ (ys : Fin m → S → ℝ) (_ : ∑ i, ys i = y), ∑ i, conj (f i) (ys i) := by sorry

end Supplement

end ConvexRMDP
