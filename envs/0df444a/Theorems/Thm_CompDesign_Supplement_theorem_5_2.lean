-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_5_2
-- name    : CompDesign.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:54:19.189934+00:00
-- url     : https://prove2.me/theorems/1c442a51-3789-4b9a-8c7f-e0cc346e0d9e
-- title:
--   Theorem 5.2 — a cost-oblivious rule that guarantees equilibria has an additive instance with $\mathrm{OPT}/v(S)\ge2$
-- statement:
--   Fix $\lambda\in(0,1)$ and a budget $B>0$. A deterministic **cost-oblivious** payment rule assigns to each number of agents $n$ and each value function $v$ on $N=\{1,\dots,n\}$ payments $p_i(S)$, without seeing the costs. Suppose that for every $n$ and every additive value function $v$ ($v(S)=\sum_{i\in S}v_i$, $v_i\ge0$) the rule is nonnegative, budget feasible ($\sum_ip_i(S)\le B$ for all $S$), and guarantees a pure Nash equilibrium for every cost vector with $0\le c_i\le\lambda B$.
--
--   **Theorem 5.2 (Lower bound without anonymity).** Then there are $n$, an additive (hence normalized and monotone) $v$ and costs $0\le c_i\le\lambda B$ for which the induced game has a pure Nash equilibrium $S$ with
--   $$\frac{\mathrm{OPT}}{v(S)}\ \ge\ 2,$$
--   where $\mathrm{OPT}=\max\{v(T):\sum_{i\in T}c_i\le B\}$ and the ratio is $+\infty$ when $\mathrm{OPT}>0=v(S)$. As a result, no such rule can guarantee $\mathrm{PoA}_{\mathrm{PNE}}<2$.
--
--   Together with Theorem 5.1, this shows that the factor 2 of the marginal-contribution rule is optimal among cost-oblivious rules as $\lambda\to0$.
--
--   Differences from the source:
--   - generalization: a rule of (N, v, B), nonnegative, budget feasible and guaranteeing equilibria at every budget → a rule P n v at one fixed budget B > 0, with the hypotheses at that B; the instance has budget B; reason: weaker hypotheses: any rule of the source restricted to one budget satisfies them, so the Lean statement implies the source's
--   - generalization: hypotheses on the rule for every value function → nonnegativity, budget feasibility and the equilibrium guarantee assumed only for additive v; reason: weaker hypotheses; the conclusion's instance is additive, so the Lean statement implies the source's
--   - encoding: max_i c_i/B ≤ λ → 0 ≤ c_i ≤ λ·B for every i; reason: equivalent for B > 0, with the standing c ≥ 0
--   - encoding: OPT/v(S) ≥ 2 with the +∞ convention of (5) → 0 < OPT ∧ 2·v(S) ≤ OPT; reason: exactly the convention of (5); excludes 0/0
--   - encoding: "as a result, no such rule can guarantee PoA_PNE < 2" → no separate clause; reason: it is the displayed conclusion restated
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 5.2, §5.2.2, p.29 (PDF 32)

import Mathlib
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsPNEOf
import Definitions.Def_FairShares_IsAdditive

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 5.2 (Lower bound without anonymity), §5.2.2, p.29 (PDF 32) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Fix any
`λ ∈ (0,1)`. Consider any deterministic payment rule that is nonnegative, budget feasible, cost
oblivious, and guarantees the existence of a pure Nash equilibrium for every cost vector satisfying
`max_i c_i/B ≤ λ`. Then there is an instance with a normalized monotone additive value function `v`
and a cost vector satisfying `max_i c_i/B ≤ λ` for which the induced game has a pure Nash equilibrium
`S` such that `OPT/v(S) ≥ 2`.

**Formalization Note.** `λ` is `l`. Cost obliviousness is structural: the rule `P` maps a number of
agents `n` and a value function `v` to payments `P n v S i`, and never sees `c`; it is given for
every `n` (the proof chooses `n = 2⌊1/λ⌋ + 1`). The budget `B > 0` is fixed and the hypotheses on `P`
(nonnegativity, budget feasibility `∑_i p_i(S) ≤ B`, existence of a pure Nash equilibrium) are
assumed only for additive `v` (`v(S) = ∑_{i∈S} v_i`, `v_i ≥ 0`), the class the conclusion uses.
`OPT/v(S) ≥ 2` is `0 < OPT ∧ 2 v(S) ≤ OPT`, the convention of (5) (`+∞` when `OPT > 0 = v(S)`). Additivity is the published
`FairShares.IsAdditive` (nonnegative item values `v_i`, `v(S) = ∑_{i∈S} v_i`). -/
theorem theorem_5_2 (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) (B : ℝ) (hB : 0 < B)
    (P : (n : ℕ) → (Finset (Fin n) → ℝ) → Finset (Fin n) → Fin n → ℝ)
    (hnn : ∀ (n : ℕ) (v : Finset (Fin n) → ℝ), FairShares.IsAdditive v → ∀ S i, 0 ≤ P n v S i)
    (hbf : ∀ (n : ℕ) (v : Finset (Fin n) → ℝ), FairShares.IsAdditive v → ∀ S, ∑ i, P n v S i ≤ B)
    (hex : ∀ (n : ℕ) (v : Finset (Fin n) → ℝ), FairShares.IsAdditive v → ∀ c : Fin n → ℝ,
      (∀ i, 0 ≤ c i ∧ c i ≤ l * B) → ∃ S, IsPNEOf (P n v) c S) :
    ∃ (n : ℕ) (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n)), FairShares.IsAdditive v ∧
      (∀ i, 0 ≤ c i ∧ c i ≤ l * B) ∧ IsPNEOf (P n v) c S ∧
      0 < CompDesignBFM.OPT v B c ∧ 2 * v S ≤ CompDesignBFM.OPT v B c := by sorry

end CompDesign.Supplement
