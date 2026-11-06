-- Prove2me | Theorems.Thm_CompetingSellers_lemma_2_3
-- name    : CompetingSellers.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:05:45.398433+00:00
-- url     : https://prove2.me/theorems/c5e9e930-a608-419e-b14a-ccb3e3bc383e
-- title:
--   Lemma 2.3 (Myerson) — implementable allocation rules and the payment identity
-- statement:
--   Let $z:[0,\infty)\to[0,1]$ be an allocation rule. Then $z$ is implementable (it implements some proper pricing function) if and only if $z$ is non-decreasing. In that case there is a unique proper pricing function $P$ implemented by $z$, and
--   $$P(z(\hat v))=\hat v\,z(\hat v)-\int_0^{\hat v}z(u)\,du\qquad\text{for all }\hat v\ge0.$$
--
--   This is the single-seller characterization the paper uses to pass between allocation rules and menus; the equalizers of Definitions 3.12 and 3.17 are defined through their allocation rules.
--
--   **Formalization Note** $z$ is a real function with values in $[0,1]$ on $[0,\infty)$. Uniqueness of $P$ is on $[0,1]$. The payment identity is stated for every proper $P$ implemented by $z$.
--
--   Differences from the source:
--   - encoding: allocation rule z : [0, ∞) → [0, 1]; P : [0, 1] → ℝ≥0 ∪ {∞} → z : ℝ → ℝ with z v ∈ [0, 1] for v ≥ 0; P : ℝ → ℝ≥0∞ and uniqueness as equality on [0, 1]; reason: values outside the domains are never used; same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 2.3, p.18 (PDF 21); restated p.55 (PDF 58)

import Mathlib
import Definitions.Def_CompetingSellers_utilP

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 2.3 (Implementable Allocation Rules, Myerson [Mye81]).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 2.3, p.18 (PDF 21; restated p.55): "An allocation rule `z : [0, ∞) → [0, 1]` is
implementable if and only if it is non-decreasing. In this case, there exists a unique proper
pricing function `P` implemented by `z`. Moreover, `P(z(v̂)) = v̂ · z(v̂) − ∫_0^v̂ z(u) du`, for
all `v̂ ≥ 0`."

**Formalization Note.** An allocation rule is `z : ℝ → ℝ` with values in `[0, 1]` on `[0, ∞)`;
non-decreasing means monotone on `[0, ∞)`. Uniqueness of `P` is on its domain `[0, 1]`. The
payment identity is stated for every proper `P` implemented by `z` (there is only one);
`P(z(v̂))` is finite because `z(v̂)` is an available allocation. -/
theorem lemma_2_3 (z : ℝ → ℝ) (hz : ∀ v, 0 ≤ v → z v ∈ Set.Icc (0 : ℝ) 1) :
    (Implementable z ↔ MonotoneOn z (Set.Ici 0)) ∧
    (MonotoneOn z (Set.Ici 0) →
      (∃ P : ℝ → ℝ≥0∞, IsProperPricing P ∧ Implements z P ∧
        ∀ P' : ℝ → ℝ≥0∞, IsProperPricing P' → Implements z P' → Set.EqOn P' P (Set.Icc 0 1)) ∧
      ∀ P : ℝ → ℝ≥0∞, IsProperPricing P → Implements z P → ∀ v, 0 ≤ v →
        (P (z v)).toReal = v * z v - ∫ u in (0 : ℝ)..v, z u) := by sorry

end CompetingSellers
