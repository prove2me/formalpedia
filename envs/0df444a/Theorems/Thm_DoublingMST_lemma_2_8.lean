-- Prove2me | Theorems.Thm_DoublingMST_lemma_2_8
-- name    : DoublingMST.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:53.710871+00:00
-- url     : https://prove2.me/theorems/d898248d-4e5c-4ba4-9ad9-ea55836e1a87
-- title:
--   Lemma 2.8 — bounded branching of the net hierarchy
-- statement:
--   There is an absolute constant $C>0$ with the following property. Assume $|X|\ge2$, minimum interpoint distance $>1$, and let $N$ be a net hierarchy. For every level $\ell\le L$ and $u\in N_\ell$:
--
--   1. $|C(u)|\le2^{C\cdot\operatorname{ddim}(X)}$;
--   2. for every level $k$ with $\ell<k\le L$, at most $2^{C\cdot\operatorname{ddim}(X)}$ points $w\in N_k$ have $u$ as a descendant.
--
--   These bounds control the cost of descending the hierarchy.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - encoding: the §2.1 standing assumption that the minimum interpoint distance of X is greater than 1 (p.12) → hypothesis MinDistGtOne d; reason: the source assumes it throughout §§2.1–4 (it is what makes level-0 balls singletons)
--   - reading: 2^{O(ddim)} → ∃ C > 0, chosen before the space, with bound 2^{C · ddim(X)}; reason: the standard meaning of the O; ddim is that of X
--   - encoding: u is the descendant of at most … level-k net points → the number of w ∈ N_k with u ∈ D_ℓ(w), for ℓ < k ≤ L; reason: levels above L are not levels of the hierarchy
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 2.8, p.13 (PDF p.15); proof p.49 (PDF p.51)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_MinDistGtOne
import Definitions.Def_DoublingMST_ddim
import Definitions.Def_DoublingMST_children
import Definitions.Def_DoublingMST_descendants
open scoped Classical

namespace DoublingMST

/-- **Lemma 2.8 (bounded branching).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 2.8, p.13 (PDF p.15): "Let u ∈ N_ℓ be a level-ℓ net point. Then (1) |C(u)| ≤ 2^{O(ddim)}.
(2) For each k > ℓ, u is the descendant of at most 2^{O(ddim)} level-k net points."

There is an absolute `C > 0` such that, under the standing assumptions of §2.1, for every net
hierarchy `H`, level `ℓ ≤ L` and `u ∈ N_ℓ`:
1. `|C(u)| ≤ 2^{C · ddim(X)}`;
2. for every level `k` with `ℓ < k ≤ L`, at most `2^{C · ddim(X)}` points `w ∈ N_k` have `u ∈ D_ℓ(w)`.

**Formalization Note.** The `O` is one absolute `C`, placed before the space; `ddim` is that of
`X`. Levels above `L` are not levels of the hierarchy, so `k ≤ L`. -/
theorem lemma_2_8 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ d : Fin n → Fin n → ℝ, IsMetric d →
    MinDistGtOne d → ∀ (H : NetHierarchy d) (ℓ : ℕ), ℓ ≤ topLevel d → ∀ u ∈ H.N ℓ,
      ((children H (u, ℓ)).card : ℝ) ≤ (2 : ℝ) ^ (C * ddim d) ∧
      ∀ k : ℕ, ℓ < k → k ≤ topLevel d →
        (((H.N k).filter fun w => u ∈ descendants H (w, k) ℓ).card : ℝ) ≤
          (2 : ℝ) ^ (C * ddim d) := by sorry

end DoublingMST
