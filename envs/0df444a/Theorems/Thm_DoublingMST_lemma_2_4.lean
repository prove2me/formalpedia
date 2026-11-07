-- Prove2me | Theorems.Thm_DoublingMST_lemma_2_4
-- name    : DoublingMST.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:41.586344+00:00
-- url     : https://prove2.me/theorems/fbd7b871-bd0f-4908-81b2-659a1fa47747
-- title:
--   Lemma 2.4 — packing property [GKL03]
-- statement:
--   There is an absolute constant $C>0$ such that for every finite metric space $(X,d)$ with $|X|\ge2$, every $\rho>0$ and every $\rho$-packing $S\subseteq X$,
--
--   $$|S|\le\left(2+\frac{\operatorname{diam}(S)}{\rho}\right)^{C\cdot\operatorname{ddim}(S)},$$
--
--   where $\operatorname{ddim}(S)$ is the doubling dimension of $(S,d)$.
--
--   This counting bound is used throughout to bound the number of net points in a ball.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - reading: (2 + diam(S)/ρ)^{O(ddim(S))} → ∃ C > 0, chosen before the space, with exponent C · ddim(S); reason: the standard meaning of the O; one absolute constant
--   - encoding: ρ-packing (Definition 2.3, for ρ > 0) → hypotheses 0 < ρ and IsPacking d S ρ; reason: Definition 2.3's range of ρ
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 2.4, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_IsPacking
import Definitions.Def_DoublingMST_diam
import Definitions.Def_DoublingMST_ddimOn
open scoped Classical

namespace DoublingMST

/-- **Lemma 2.4 (Packing Property [GKL03]).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 2.4, p.12 (PDF p.14): "If S is ρ-packing, then |S| ≤ (2 + diam(S)/ρ)^{O(ddim(S))}."

There is an absolute constant `C > 0` such that for every metric `d` on `n ≥ 2` points, every
`ρ > 0` and every ρ-packing `S`, `|S| ≤ (2 + diam(S)/ρ)^{C · ddim(S)}`.

**Formalization Note.** The `O` is one absolute `C`, chosen before the space. `ddim(S)` is the
doubling dimension of `(S, d)` (`ddimOn`). The exponent is a real power of a base `≥ 2`. -/
theorem lemma_2_4 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ d : Fin n → Fin n → ℝ, IsMetric d →
    ∀ (S : Finset (Fin n)) (ρ : ℝ), 0 < ρ → IsPacking d S ρ →
      (S.card : ℝ) ≤ (2 + diam d S / ρ) ^ (C * ddimOn d S) := by sorry

end DoublingMST
