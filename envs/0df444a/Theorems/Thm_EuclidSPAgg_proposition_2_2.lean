-- Prove2me | Theorems.Thm_EuclidSPAgg_proposition_2_2
-- name    : EuclidSPAgg.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:39:48.222742+00:00
-- url     : https://prove2.me/theorems/bbbc37eb-9e3f-4557-bb00-22a72fb7270a
-- title:
--   Proposition 2.2 — a continuous one-report strategyproof map is the projection onto its closed convex range
-- statement:
--   Let $T:E\to E$ be continuous and satisfy
--   $$
--   \|a-T(a)\|\le\|a-T(b)\|\qquad(a,b\in E).
--   $$
--   Then $C=T(E)$ is closed and convex, and $T=P_C$: for every $a\in E$, $T(a)$ is the unique point of $C$ nearest to $a$.
--
--   This one-report characterization (Kim–Roush; Peters–van der Stel–Storcken) is applied to every coalition diagonal and every unilateral response of a continuous strategyproof mechanism.
--
--   **Formalization Note** $T=P_C$ is stated as: the set of nearest points of $C$ to $a$ is exactly $\{T(a)\}$.
--
--   Differences from the source:
--   - encoding: T = P_C → for every a, SuperPolyak.nearestPoints (range T) a = {T a}; reason: the nearest point of the closed convex range exists, is unique and equals T(a), which is what T = P_C means
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Proposition 2.2, display (2.4), p.10 (PDF p.12)

import Mathlib
import Definitions.Def_SuperPolyak_solutionSet
import Definitions.Def_RBMSensitivity_E
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Proposition 2.2** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.10 (PDF p.12)). Suppose `T : E → E` is continuous and
`‖a − T(a)‖ ≤ ‖a − T(b)‖` for all `a, b ∈ E` (display (2.4)). Then `C = T(E)` is closed and
convex, and `T = P_C`.

**Formalization Note** `T = P_C` is stated as: for every `a`, the nearest-point set of `C` to `a`
is exactly `{T a}` (so the nearest point exists, is unique, and equals `T a`). `d ≥ 1` is the
paper's standing assumption (p.8). -/
theorem proposition_2_2 {d : ℕ} (hd : 1 ≤ d) (T : E d → E d) (hT : Continuous T)
    (hSP : ∀ a b : E d, ‖a - T a‖ ≤ ‖a - T b‖) :
    IsClosed (Set.range T) ∧ Convex ℝ (Set.range T) ∧
      ∀ a : E d, SuperPolyak.nearestPoints (Set.range T) a = {T a} := by sorry

end EuclidSPAgg
