-- Prove2me | Theorems.Thm_CompDesignBFM_Supplement_theorem_3_6
-- name    : CompDesignBFM.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:06:49.838969+00:00
-- url     : https://prove2.me/theorems/8d74db0c-c08e-4ed3-a8de-baf6a58c96b5
-- title:
--   Theorem 3.6 — constant PoS for monotone subadditive via $\tilde v$: $2e+1$ by mixing, $2e^{1/(1-\lambda)}$ and $2e/(1-\theta)$ in large markets
-- statement:
--   Let $v:2^N\to\mathbb R$ be a normalized ($v(\emptyset)=0$), monotone, subadditive function, $\tilde v$ its smoothing (Definition 3.1) and $B>0$ a budget. Write $\mathrm{OPT}$ and $M$ for the benchmarks of $v$, $p^{\tilde v}$ for the marginal-contribution rule run over $\tilde v$ and $p^{\mathrm{sing}}$ for the singleton rule over $v$. Then:
--
--   1. The randomized rule that runs $p^{\tilde v}$ with probability $\frac{2e}{2e+1}$ and $p^{\mathrm{sing}}$ with probability $\frac1{2e+1}$ is a valid compensation rule and has price of stability at most $2e+1$: for every $c\ge0$ there are $S_1\in E(p^{\tilde v},c)$ and $S_2\in E(p^{\mathrm{sing}},c)$ with
--   $$\mathrm{OPT}\le(2e+1)\Bigl(\tfrac{2e}{2e+1}v(S_1)+\tfrac1{2e+1}v(S_2)\Bigr).$$
--   2. If $c_i/B\le\lambda<1$ for every $i$, some $S\in E(p^{\tilde v},c)$ has $\mathrm{OPT}\le2e^{1/(1-\lambda)}\,v(S)$.
--   3. If $M/\mathrm{OPT}\le\theta<1$, some $S\in E(p^{\tilde v},c)$ has $\mathrm{OPT}\le\frac{2e}{1-\theta}\,v(S)$.
--
--   Equilibria are those of the rule over $\tilde v$; values are measured by $v$. Running the rule over the self-bounding proxy $\tilde v$ costs only a factor $2$ against the XOS case.
--
--   **Formalization Note** The singleton rule breaks ties by an injective agent priority $\rho$, fixed before the costs; the claim is made for every such $\rho$.
--
--   Differences from the source:
--   - encoding: Let v be a monotone subadditive function → adds v ∅ = 0; reason: the paper's standing normalization (p.1: we generally assume that v is normalized); the smoothing and Theorem 3.5 use it
--   - generalization: there is a randomized payment rule (the singleton rule's tie-breaking unspecified) → for every injective agent priority ρ, the mixture whose singleton branch breaks ties by ρ; reason: an injective priority exists (the agent index), so the statement specializes to the existence claim
--   - encoding: a randomized payment rule (a distribution over budget-feasible deterministic rules, p.5) → both branches asserted IsCompRule B: nonnegative, zero outside S, budget feasible; reason: this is the definition of a compensation rule on p.5, made an explicit conjunct
--   - encoding: PoS(P, c) ≤ α, the ratio of OPT to the expected best-equilibrium value → existence of equilibria S₁ (marginal-contribution branch) and S₂ (singleton branch), resp. S, with OPT ≤ α·(weighted values); reason: the equilibrium sets are finite, so the best equilibrium is attained; the form also asserts the existence the paper assumes and avoids the ratio's division by zero
--   - reading: PoS of 2e^{1/(1−λ)}, PoS of 2e/(1−θ) → PoS at most these values; reason: the proof is a lower bound on the best equilibrium; equality is not claimed
--   - encoding: M/OPT ≤ θ → M ≤ θ·OPT; reason: the same condition when OPT > 0; at OPT = 0 the claim OPT ≤ α·v(S) holds for any equilibrium S since v ≥ 0
--   - encoding: the asymptotic rewrites = 2e + o_λ(1), = 2e + o_θ(1) → omitted; reason: they restate the limit of the explicit bound and add no claim about the rule
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem 3.6, p.18 (PDF 20)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_BudgetClock_Subadditive_Setting
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesignBFM_M
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_smoothed
import Definitions.Def_CompDesignBFM_Supplement_IsPNEOf
import Definitions.Def_CompDesignBFM_Supplement_IsCompRule
import Definitions.Def_CompDesignBFM_Supplement_singletonPay

namespace CompDesignBFM

namespace Supplement

/-- Theorem 3.6 (constant PoS bounds for monotone subadditive functions), Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.18, PDF 20. Let `v`
be a normalized monotone subadditive function, `ṽ` its smoothing (Definition 3.1), and `B > 0`.
1. The randomized payment rule that runs the marginal-contribution rule over `ṽ` with probability
   `2e/(2e+1)` and the singleton rule over `v` with probability `1/(2e+1)` has PoS at most `2e + 1`.
2. If `cᵢ/B ≤ λ < 1` for all `i`, the marginal-contribution rule over `ṽ` has PoS at most
   `2e^(1/(1−λ))`.
3. If `M/OPT ≤ θ < 1`, the marginal-contribution rule over `ṽ` has PoS at most `2e/(1−θ)`.
**Formalization Note.** Equilibria of the marginal-contribution branch are those of the rule over `ṽ`
(`IsPNE (smoothed v) B c`); values, `OPT` and `M` are those of `v`. Both branches are asserted to be
compensation rules, fixed before the costs. "PoS ≤ α" is `OPT ≤ α · E[best equilibrium value]`, written
with existential equilibria as in Theorem 3.4; "PoS of" in clauses 2–3 is read as "PoS at most".
`v ∅ = 0` is the paper's standing normalization (p.1). The singleton rule uses an injective agent
priority `rho`; the claim is made for every such `rho`. -/
theorem theorem_3_6 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (hB : 0 < B) (hv0 : v ∅ = 0)
    (hm : IsMonotoneSF v) (hsub : BudgetClock.Subadditive.IsSubadditive v)
    (rho : Fin n → ℕ) (hrho : Function.Injective rho) :
    (IsCompRule B (mcPay (smoothed v) B) ∧ IsCompRule B (singletonPay v B rho)) ∧
    (∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) →
      ∃ S₁ S₂ : Finset (Fin n), IsPNE (smoothed v) B c S₁ ∧ IsPNEOf (singletonPay v B rho) c S₂ ∧
        OPT v B c ≤ (2 * Real.exp 1 + 1) *
          (2 * Real.exp 1 / (2 * Real.exp 1 + 1) * v S₁ + 1 / (2 * Real.exp 1 + 1) * v S₂)) ∧
    (∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → ∀ l : ℝ, l < 1 → (∀ i, c i / B ≤ l) →
      ∃ S : Finset (Fin n), IsPNE (smoothed v) B c S ∧
        OPT v B c ≤ 2 * Real.exp (1 / (1 - l)) * v S) ∧
    (∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → ∀ θ : ℝ, θ < 1 → M v B c ≤ θ * OPT v B c →
      ∃ S : Finset (Fin n), IsPNE (smoothed v) B c S ∧
        OPT v B c ≤ 2 * Real.exp 1 / (1 - θ) * v S) := by sorry

end Supplement

end CompDesignBFM
