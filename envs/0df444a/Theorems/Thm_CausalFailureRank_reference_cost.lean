-- Prove2me | Theorems.Thm_CausalFailureRank_reference_cost
-- name    : CausalFailureRank.reference_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:15:55.162458+00:00
-- url     : https://prove2.me/theorems/ffff019f-314f-4104-9ea5-23ffce3a8bd5
-- title:
--   App. B.4 — reference controller cost
-- statement:
--   Let $r\to0$. For a state $(i,R)$ of finite rank $d$ and every $\varepsilon>0$, the expected observation cost of the reference controller with risk $r$ is eventually at most
--   $$(1+\varepsilon)\,C(i,R)\,\ell_d(1/r).$$
--   At infinite rank it buys no observation. On every sample its actual correction charges are at most $\min(N,q)f_{\max}$. This is the matching upper bound, before truncation.
--
--   Differences from the source:
--   - encoding: "(2) as an upper bound" → an explicit $(1+\varepsilon)$ bound with threshold $r_0$ following the selection, state and $\varepsilon$; reason: meaning of the leading-term comparison
--   - encoding: pathwise correction total → bill at most observation part plus $\min(N,q)f_{\max}$; reason: the correction part of the bill is the difference of the two
--   - encoding: stages $1,\dots,N+1$ (entry states $1,\dots,N+1$) → 0-based stages, terminal $i\ge N$, entry stage $i\le N$ as a hypothesis; reason: Lean indexing; a stage index beyond the terminal one does not exist in the source, so no instance changes
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.4, p.18

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient
import Definitions.Def_CausalFailureRank_tapeLaw
import Definitions.Def_CausalFailureRank_refController

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **Reference controller cost.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.4, p.18: "Comparing the terms therefore gives exactly (2)
as an upper bound. Every actual correction, including one on a later-failing path, is charged. Their
pathwise total is at most min(N, q)f_max, which is O(1) and does not affect any finite-depth divergent
leading term."

**Formalization Note.** Three clauses: the expected observation cost at finite rank, with the threshold
`r₀` following `sel`, `i`, `R`, `ε`; no observation at infinite rank (rule 1); the pathwise correction
bill, as `bill ≤ observation part + min(N,q) f_max`. -/
theorem reference_cost (I : Instance N q) (sel : Fin N → Finset (Fin q) → Option (Fin q))
    (hsel : IsBadChildSelection I sel) (i : ℕ) (hi : i ≤ N) (R : Finset (Fin q)) :
    (∀ d : ℕ, rank I i R = d → ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → r ≤ 1 / 4 →
      ∫⁻ ω, obsBillFrom I .currentPay (noCaps N) (refAction I sel none i R r) (entryState I i R) ω
          ∂(tapeLaw I) ≤
        ENNReal.ofReal ((1 + ε) * C I i R * iterLog d (1 / r))) ∧
    (rank I i R = ⊤ → ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ ω,
      obsBillFrom I .currentPay (noCaps N) (refAction I sel none i R r) (entryState I i R) ω = 0) ∧
    ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ ω,
      billFrom I .currentPay (noCaps N) (refAction I sel none i R r) (entryState I i R) ω ≤
        obsBillFrom I .currentPay (noCaps N) (refAction I sel none i R r) (entryState I i R) ω +
          ENNReal.ofReal ((min N q : ℕ) * fmax I) := by sorry

end CausalFailureRank
