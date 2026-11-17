-- Prove2me | Theorems.Thm_FairFacilityLoc_Supplement_theorem_E_3
-- name    : FairFacilityLoc.Supplement.theorem_E_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:29:56.741563+00:00
-- url     : https://prove2.me/theorems/3fbacc8c-f189-4bd5-b122-530de7e0c309
-- title:
--   Theorem E.3 — no finite ratio on superlinear group effects
-- statement:
--   Fix a positive dimension $d$ and $0<\varepsilon<1$. The function
--
--   $$
--   E_\varepsilon(s,t)=\frac{\min\{s,t\}+\varepsilon\max\{s,t\}}{1+\varepsilon}
--   $$
--
--   is a nonzero, monotone, symmetric and superlinear group effect, and $E_\varepsilon(1,1)=1$.
--
--   Every deterministic strategyproof mechanism has ratio at least
--
--   $$
--   \frac{1}{4\varepsilon}
--   $$
--
--   on the fixed structure of two disjoint two-agent groups, both using $E_\varepsilon$. Consequently, the supremum of its ratio over all superlinear group effects is infinite. This holds in every positive dimension and requires neither anonymity, continuity nor coordinate independence.
--
--   The finite bound belongs to each fixed $\varepsilon$; the infinite class-wide conclusion ranges over the whole family as $\varepsilon$ approaches zero.
--
--   **Formalization Note** The ratio is valued in $[0,\infty]$ with $0/0=1$ and $a/0=\infty$ for $a>0$.
--
--   Differences from the source:
--   - encoding: every dimension → a natural number $d$ with $1\le d$ and locations in `EuclideanSpace ℝ (Fin d)`; reason: the paper’s Euclidean dimensions are positive
--   - encoding: $0<\varepsilon<1$ real and $E_\varepsilon$ on two nonnegative real coordinates → `ε : ℝ≥0` with the same strict bounds and `epsilonEffect ε : (Fin 2 → ℝ≥0) → ℝ≥0`; reason: positivity makes the parameter nonnegative, and `Fin 2` is the same two-coordinate domain with 0-based indexing
--   - encoding: the group structure of Lemma E.2 → `epsilonTwoByTwo ε` on `Fin 4` agents and `Fin 2` groups; reason: it fixes labels for the same two disjoint two-agent groups
--   - encoding: mechanisms and ratios range over group effects in the sense of Definition 2.1 → `GeneralMechanism` is total on raw `GeneralGroupStructure` data while `GeneralIsStrategyproof` and `superlinearRatio` explicitly require `IsGeneralGroupStructure`; reason: separating admissibility keeps the printed group-effect conclusion for $E_\varepsilon$ visible, and raw inadmissible inputs are excluded from every semantic quantifier
--   - encoding: ratio at least $1/(4\varepsilon)$ and no finite ratio on the class → an inequality and `superlinearRatio M = ⊤` in $[0,\infty]$; reason: top is exactly the absence of a finite upper bound
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Theorem E.3, pp.91–92 (PDF pp.93–94), equation (E.3)

import Mathlib
import Definitions.Def_FairFacilityLoc_Supplement_epsilonEffect

open scoped NNReal ENNReal

namespace FairFacilityLoc.Supplement

set_option autoImplicit false

/-- **Theorem E.3** (Yan–Zhou, *Fair and Strategyproof Facility Location in Euclidean Space*,
manuscript, sha256 642a1268…, pp.91–92, PDF pp.93–94). For `0 < ε < 1`, the exact effect
`E_ε(s,t) = (min{s,t} + ε max{s,t})/(1+ε)` is monotone, symmetric, superlinear and normalized
by `E_ε(1,1)=1`. Every strategyproof mechanism has ratio at least `1/(4ε)` on the fixed
two-disjoint-two-agent structure using this effect. Consequently its ratio over all superlinear
group effects is infinite, in every positive dimension.

**Formalization Note.** The first conjunct packages “monotone, symmetric” together with the
paper's standing nonzero condition as `IsGroupEffect`. The exact four-agent structure is
`epsilonTwoByTwo ε`. Ratios are in `ℝ≥0∞` with `0/0=1` and `a/0=∞`. No anonymity,
continuity, coordinate independence, or finite-ratio hypothesis is imposed. -/
theorem theorem_E_3 (d : ℕ) (hd : 1 ≤ d) (ε : ℝ≥0) (hε0 : 0 < ε) (hε1 : ε < 1)
    (M : GeneralMechanism d) (hsp : GeneralIsStrategyproof M) :
    FairFacilityLoc.IsGroupEffect (epsilonEffect ε) ∧
      IsSuperlinearEffect (epsilonEffect ε) ∧
      epsilonEffect ε 1 = 1 ∧
      (((1 / (4 * ε) : ℝ≥0) : ℝ≥0∞) ≤ ratioOn M (epsilonTwoByTwo ε)) ∧
      superlinearRatio M = ⊤ := by sorry

end FairFacilityLoc.Supplement
