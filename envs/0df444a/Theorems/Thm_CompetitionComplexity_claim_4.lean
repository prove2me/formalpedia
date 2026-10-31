-- Prove2me | Theorems.Thm_CompetitionComplexity_claim_4
-- name    : CompetitionComplexity.claim_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:14.218987+00:00
-- url     : https://prove2.me/theorems/4fad6a17-0ef6-4df1-b95e-7864b2720a6f
-- title:
--   Claim 4 — for $0<\varepsilon'\le\varepsilon$, $\rho_{\varepsilon',j}$ is well defined when $\rho_{\varepsilon,j}$ is, and $\rho_{\varepsilon',j}\ge\rho_{\varepsilon,j}$
-- statement:
--   Let $n\ge2$ be an integer and $0<\varepsilon'\le\varepsilon$. For every positive integer $j$: if $\rho_{\varepsilon,j}$ of the recursion (9) is well defined, then $\rho_{\varepsilon',j}$ is well defined and
--   $$
--   \rho_{\varepsilon',j}\ge\rho_{\varepsilon,j}.
--   $$
--   In the proof of Theorem 2 this is applied with $\varepsilon'$ chosen so that $m/n=\phi(\varepsilon')$, to compare the recursion at $\varepsilon$ with the differential equation at $\varepsilon'$.
--
--   Differences from the source:
--   - generalization: ε′ > 0 defined by m/n = ϕ(ε′), with ε′ ≤ ε → every ε′ with 0 < ε′ ≤ ε, and every n ≥ 2; reason: the claim's induction uses only ε′ ≤ ε; the source's ε′ is one such value, so the Lean statement specializes to it
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Claim 4, p.28 (in the proof of Theorem 2)

import Mathlib
import Definitions.Def_CompetitionComplexity_Recursion

namespace CompetitionComplexity

/-- **Claim 4** (in the proof of Theorem 2).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Claim 4, p.28:
"For every positive integer j, ρε′,j is well defined when ρε,j is well defined, and ρε′,j ≥ ρε,j."
Context (same page): `ε > 0`, `n ≥ 2`, and `ε′ > 0` with `m/n = ϕ(ε′)` and `ε′ ≤ ε`.

**Formalization Note.** Stated for every `n ≥ 2` and every `0 < ε′ ≤ ε`: the defining equation
`m/n = ϕ(ε′)` of `ε′` is not used by the claim (its proof is an induction using only `ε′ ≤ ε`). `j` is positive because `WellDef` says so. -/
theorem claim_4 (n : ℕ) (hn : 2 ≤ n) (ε ε' : ℝ) (hε' : 0 < ε') (hle : ε' ≤ ε) (j : ℕ)
    (hw : WellDef ε n j) :
    WellDef ε' n j ∧ rho ε n j ≤ rho ε' n j := by sorry

end CompetitionComplexity
