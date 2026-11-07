-- Prove2me | Theorems.Thm_EuclidSPAgg_theorem_7_1
-- name    : EuclidSPAgg.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:14.611188+00:00
-- url     : https://prove2.me/theorems/aec9b055-6a84-4008-999e-736ac578b5a8
-- title:
--   Theorem 7.1 — a strategyproof mechanism is continuous if and only if its full range is convex
-- statement:
--   Let $f:E^n\to E$ be strategyproof. Then $f$ is continuous if and only if its full range
--   $$
--   \mathcal R(f)=f(E^n)
--   $$
--   is convex.
--
--   This extends the planar theorem of Peters, van der Stel and Storcken to every finite dimension. It yields automatic continuity of unanimous strategyproof mechanisms (Corollary 7.2).
--
--   Differences from the source: none.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 7.1, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Theorem 7.1** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.31 (PDF p.33)). Let `f : Eⁿ → E` be strategyproof. Then `f` is
continuous if and only if its full range `R(f) = f(Eⁿ)` is convex.

**Formalization Note** The full range is `Set.range f`. `n ≥ 1` and `d ≥ 1` are the paper's
standing assumptions (p.8). -/
theorem theorem_7_1 {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (f : Mech n d) (hf : IsStrategyproof f) :
    Continuous f ↔ Convex ℝ (Set.range f) := by sorry

end EuclidSPAgg
