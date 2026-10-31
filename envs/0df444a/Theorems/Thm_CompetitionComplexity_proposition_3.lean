-- Prove2me | Theorems.Thm_CompetitionComplexity_proposition_3
-- name    : CompetitionComplexity.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:37.004161+00:00
-- url     : https://prove2.me/theorems/4ebb6481-d21f-40e6-bda1-589a18f64137
-- title:
--   Proposition 3 — the minimizer $Y$ is non-increasing and log-convex
-- statement:
--   Let $\varepsilon>0$, let $n\ge2$ and $m\ge3$ be integers with $\rho_{\varepsilon,m}$ well defined, and let $Y_j=\prod_{k=0}^{j-1}\rho_{\varepsilon,m-k}$ as in (10). Then:
--
--   1. **(a)** $Y_{j+1}\le Y_j$ for every $j\in\{1,\dots,m-1\}$;
--   2. **(b)** $Y_j^2\le Y_{j-1}Y_{j+1}$ for every $j\in\{2,\dots,m-1\}$.
--
--   Together with Proposition 2 this makes $(1,Y_1,\dots,Y_{m-1})$, continued geometrically, feasible for (2)–(4), which gives the upper bound in Lemma 4.
--
--   **Formalization Note** At $j=m-1$ both parts use $Y_m=\prod_{k=0}^{m-1}\rho_{\varepsilon,m-k}$, the product formula of (10) at $j=m$.
--
--   Differences from the source:
--   - encoding: Yₘ (used at j = m − 1, with Yₘ/Yₘ₋₁ = ρ_{ε,1} = 1 in the proof) → Yₘ = Π_{k=0}^{m−1} ρ_{ε,m−k}; reason: the product formula of (10) at j = m, which is what the proof uses
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Proposition 3, p.17

import Mathlib
import Definitions.Def_CompetitionComplexity_Recursion
import Definitions.Def_CompetitionComplexity_Gamma

namespace CompetitionComplexity

/-- **Proposition 3.**
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Proposition 3, p.17:
"Let ε > 0, let n ≥ 2 and m ≥ 3 be two positive integers such that ρε,m is well defined, and let Y
be as defined in (10). Then, the following holds:
(a) For every j ∈ {1,...,m−1} we have that Yj+1 ≤ Yj.
(b) For every j ∈ {2,...,m−1} we have that Y²_j ≤ Yj−1Yj+1."

**Formalization Note.** `Yseq ε n m j = Π_{k=0}^{j−1} ρ_{ε,m−k}` for every `j`; at `j = m` this is
the `Yₘ` used by (a) and (b) at `j = m − 1` (the proof uses `Yₘ/Y_{m−1} = ρ_{ε,1} = 1`). -/
theorem proposition_3 (ε : ℝ) (hε : 0 < ε) (n m : ℕ) (hn : 2 ≤ n) (hm : 3 ≤ m)
    (hw : WellDef ε n m) :
    (∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → Yseq ε n m (j + 1) ≤ Yseq ε n m j) ∧
    (∀ j : ℕ, 2 ≤ j → j ≤ m - 1 →
      Yseq ε n m j ^ 2 ≤ Yseq ε n m (j - 1) * Yseq ε n m (j + 1)) := by sorry

end CompetitionComplexity
