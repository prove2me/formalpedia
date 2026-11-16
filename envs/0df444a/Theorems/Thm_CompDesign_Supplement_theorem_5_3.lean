-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_5_3
-- name    : CompDesign.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:54:53.600794+00:00
-- url     : https://prove2.me/theorems/5b787770-94ea-4213-b4c3-e22722acc2f5
-- title:
--   Theorem 5.3 — every deterministic cost-oblivious rule has an additive $n$-agent instance with a strict equilibrium and $\mathrm{OPT}/v(S)\ge\sqrt{n-1}$
-- statement:
--   Fix $n\ge3$ and a budget $B>0$. A deterministic **cost-oblivious** payment rule assigns to each value function $v$ on $N=\{1,\dots,n\}$ payments $p_i(S)$, without seeing the costs. Assume that, for every additive $v$, the payments are nonnegative and budget feasible ($\sum_ip_i(S)\le B$).
--
--   **Theorem 5.3 (Deterministic cost-oblivious lower bound).** There are an additive value function $v$ and costs $c_i\ge0$ such that the induced game has a **strict** pure Nash equilibrium $S$ ($p_i(S)>c_i$ for $i\in S$, $p_i(S\cup\{i\})<c_i$ for $i\notin S$) with
--   $$\frac{\mathrm{OPT}}{v(S)}\ \ge\ \sqrt{n-1},$$
--   the ratio being $+\infty$ when $\mathrm{OPT}>0=v(S)$.
--
--   Without a large-market assumption, no deterministic cost-oblivious rule has bounded price of anarchy, even if ties are broken in the principal's favor; randomization (Theorem 5.4) restores a constant.
--
--   Differences from the source:
--   - generalization: a rule of (N, v, B), budget feasible at every budget → a rule P v at one fixed budget B > 0, with the hypotheses at that B; the instance has budget B; reason: weaker hypotheses: any rule of the source restricted to one budget satisfies them
--   - generalization: hypotheses on the rule for every value function → nonnegativity and budget feasibility assumed only for additive v; reason: weaker hypotheses; the instance is additive
--   - reading: "deterministic cost-oblivious budget-feasible payment rule" → also nonnegative payments; reason: limited liability is part of the model's definition of a payment rule, p : 2^N → ℝ^n_{≥0} (§3.1, p.13), and the proof (case 2b) uses it
--   - encoding: OPT/v(S) ≥ √(n − 1) with the +∞ convention of (5) → 0 < OPT ∧ √(n − 1)·v(S) ≤ OPT; reason: exactly the convention of (5)
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 5.3, §5.2.3, p.31 (PDF 34)

import Mathlib
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsPNEOf
import Definitions.Def_FairShares_IsAdditive

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 5.3 (Deterministic cost-oblivious lower bound), §5.2.3, p.31 (PDF 34) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). For
every `n ≥ 3` and every deterministic cost-oblivious budget-feasible payment rule `p`, there is an
instance with `n` agents and an additive value function `v` such that the induced game has a strict
pure Nash equilibrium `S` satisfying `OPT/v(S) ≥ √(n − 1)`.

**Formalization Note.** Cost obliviousness is structural: the rule `P` maps a value function `v` on
`n` agents to payments `P v S i` and never sees `c`. The budget `B > 0` is fixed. Payments are
nonnegative (the model's limited liability, §3.1, p.13: `p : 2^N → ℝ^n_{≥0}`) and budget feasible
(`∑_i p_i(S) ≤ B`); both are assumed only for additive `v`. Costs are unrestricted (`c ≥ 0`).
`OPT/v(S) ≥ √(n−1)` is `0 < OPT ∧ √(n−1) v(S) ≤ OPT`, the convention of (5). Additivity is the published
`FairShares.IsAdditive` (nonnegative item values `v_i`, `v(S) = ∑_{i∈S} v_i`). -/
theorem theorem_5_3 (n : ℕ) (hn : 3 ≤ n) (B : ℝ) (hB : 0 < B)
    (P : (Finset (Fin n) → ℝ) → Finset (Fin n) → Fin n → ℝ)
    (hnn : ∀ v : Finset (Fin n) → ℝ, FairShares.IsAdditive v → ∀ S i, 0 ≤ P v S i)
    (hbf : ∀ v : Finset (Fin n) → ℝ, FairShares.IsAdditive v → ∀ S, ∑ i, P v S i ≤ B) :
    ∃ (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n)), FairShares.IsAdditive v ∧
      (∀ i, 0 ≤ c i) ∧ IsStrictPNEOf (P v) c S ∧ 0 < CompDesignBFM.OPT v B c ∧
      Real.sqrt ((n : ℝ) - 1) * v S ≤ CompDesignBFM.OPT v B c := by sorry

end CompDesign.Supplement
