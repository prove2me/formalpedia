-- Prove2me | Theorems.Thm_EuclidSPAgg_Supplement_theorem_9_1
-- name    : EuclidSPAgg.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:46:39.374966+00:00
-- url     : https://prove2.me/theorems/9671a22f-38b6-4d3f-a794-304b8458643d
-- title:
--   Theorem 9.1 — anonymous extraction from large populations
-- statement:
--   Fix $d\ge1$, $m\ge2$ and a real number $R$ with $1\le R<\infty$, and let $E=\mathbb R^d$. Suppose that an unbounded set of population sizes $N$ admits deterministic strategyproof mechanisms $f_N:E^N\to E$ with
--   $$
--   \mathrm{AR}(f_N)\le R .
--   $$
--   Then there exists a continuous, anonymous, unanimous, deterministic strategyproof mechanism $h:E^m\to E$ with $\mathrm{AR}(h)\le R$.
--
--   The source mechanisms need not be anonymous, continuous or unanimous. Combined with the anonymous optimality of the coordinate-wise median (Theorem 8.5), the theorem transfers the fixed-population lower bound to arbitrary large populations (Theorem 9.3).
--
--   Differences from the source:
--   - encoding: "an unbounded set of population sizes $N$ admits $f_N$" → for every $M$ there are $N\ge M$ and a strategyproof $f_N$ with $\mathrm{AR}(f_N)\le R$; reason: a set of naturals is unbounded exactly when it meets every $[M,\infty)$.
--   - encoding: the bound $R\in[1,\infty)$ → a real $R\ge1$ compared in $[0,\infty]$ as $\mathrm{ofReal}(R)$; reason: the ratio is valued in $[0,\infty]$.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 9.1, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
import Definitions.Def_EuclidSPAgg_IsUnanimous
import Definitions.Def_EuclidSPAgg_AR
open RBMSensitivity (E)

namespace EuclidSPAgg.Supplement

open EuclidSPAgg

/-- **Theorem 9.1** (anonymous extraction; Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.35 (PDF p.37)). Fix finite `d ≥ 1`, `m ≥ 2`
and `1 ≤ R < ∞`. Suppose that an unbounded set of population sizes `N` admits mechanisms
`f_N ∈ S_{N,d}` with `AR(f_N) ≤ R`. Then there exists a continuous, anonymous, unanimous,
deterministic strategyproof mechanism `h : E^m → E` with `AR(h) ≤ R`.

**Formalization Note** `R` is a real number (finite) with `1 ≤ R`, compared in `ℝ≥0∞` through
`ENNReal.ofReal`. "An unbounded set of population sizes admits …" is: for every `M` there are
`N ≥ M` and a strategyproof `f : Mech N d` with `AR f ≤ R`. The source mechanisms carry no
anonymity, continuity or unanimity hypothesis. Determinism is built in (`Mech` is a function). -/
theorem theorem_9_1 (d m : ℕ) (hd : 1 ≤ d) (hm : 2 ≤ m) (R : ℝ) (hR : 1 ≤ R)
    (hsrc : ∀ M : ℕ, ∃ N, M ≤ N ∧ ∃ f : Mech N d, IsStrategyproof f ∧ AR f ≤ ENNReal.ofReal R) :
    ∃ h : Mech m d, Continuous h ∧ IsAnonymous h ∧ IsUnanimous h ∧ IsStrategyproof h ∧
      AR h ≤ ENNReal.ofReal R := by sorry

end EuclidSPAgg.Supplement
