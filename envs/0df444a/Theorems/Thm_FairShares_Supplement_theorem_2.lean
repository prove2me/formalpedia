-- Prove2me | Theorems.Thm_FairShares_Supplement_theorem_2
-- name    : FairShares.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:28:56.826563+00:00
-- url     : https://prove2.me/theorems/63ddcf90-9ef0-43e8-aa91-ea3e88d15084
-- title:
--   Theorem 2: domination by a feasible self-maximizing share
-- statement:
--   Let $\mathcal C$ be an arbitrary class of valuation functions and let $s$ be an arbitrary share that is feasible for $\mathcal C$. Then there exists a share $s'$ for $\mathcal C$ such that $s'$ is feasible, self-maximizing, and dominates $s$ pointwise.
--
--   No additivity or computational assumption is imposed.
--
--   Differences from the source:
--   - encoding: finite item sets and all positive agent counts → items `Fin m`, shares indexed by `m,n`, and the published predicates `IsShare`, `Feasible`, `SelfMax`, and `Dominates`, each restricted to `n ≥ 1`; reason: name independence makes item names irrelevant and excludes only the undefined zero-agent case
--   - generalization: normalized nonnegative valuation functions in the paper model → an arbitrary class of real-valued bundle functions; reason: the statement uses only the share, feasibility, domination, and self-maximization predicates, and restricting the Lean class to the paper's valuation domain recovers every source instance
-- source:
--   Babaioff & Feige, arXiv:2205.07519v1, Theorem 2, p.16; proof pp.35-36

import Mathlib
import Definitions.Def_FairShares_IsShare
import Definitions.Def_FairShares_Feasible
import Definitions.Def_FairShares_SelfMax
import Definitions.Def_FairShares_Dominates

set_option autoImplicit false

namespace FairShares.Supplement

/-- **Theorem 2: every feasible share is dominated by a feasible self-maximizing share.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*,
arXiv:2205.07519v1, Theorem 2, p.16 (proof pp.35--36).

For an arbitrary valuation class `C` and arbitrary share `s` that is feasible on `C`, there is a
share `s'` that is feasible and self-maximizing on `C` and pointwise dominates `s`.

**Formalization Note.** No additivity, goods, or computability condition is imposed.  The Lean
class may contain arbitrary real-valued bundle functions, generalizing the paper model's
normalized nonnegative valuations; restricting `C` to the paper's valuation classes recovers the
source theorem.  Classes and shares range over every finite item count, and all share properties
quantify over `n ≥ 1`, exactly as in the published base definitions. -/
theorem theorem_2
    (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ)
    (hs : FairShares.IsShare C s) (hfeas : FairShares.Feasible C s) :
    ∃ s' : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
      FairShares.IsShare C s' ∧ FairShares.Feasible C s' ∧
        FairShares.Dominates C s' s ∧ FairShares.SelfMax C s' := by sorry

end FairShares.Supplement
