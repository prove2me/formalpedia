-- Prove2me | Theorems.Thm_CompDesignBFM_Supplement_theorem_3_4
-- name    : CompDesignBFM.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:06:21.307387+00:00
-- url     : https://prove2.me/theorems/f57ce6ea-94c1-4ab0-89ec-45c14583e26f
-- title:
--   Theorem 3.4 — constant PoS for monotone XOS: $e+1$ by mixing, $e^{1/(1-\lambda)}$ and $e/(1-\theta)$ in large markets
-- statement:
--   Let $v:2^N\to\mathbb R$ be a monotone XOS function and $B>0$ a budget. Write $\mathrm{OPT}=\max\{v(S):\sum_{i\in S}c_i\le B\}$, $M=\max\{v(\{i\}):c_i\le B\}$, $p^v$ for the marginal-contribution rule $p^v_i(S)=B\,(v(S)-v(S\setminus\{i\}))/v(S)$ and $p^{\mathrm{sing}}$ for the singleton rule. Then:
--
--   1. The randomized rule that runs $p^v$ with probability $\frac e{e+1}$ and $p^{\mathrm{sing}}$ with probability $\frac1{e+1}$ is a valid compensation rule and has price of stability at most $e+1$: for every cost vector $c\ge0$ there are pure equilibria $S_1\in E(p^v,c)$ and $S_2\in E(p^{\mathrm{sing}},c)$ with
--   $$\mathrm{OPT}\le(e+1)\Bigl(\tfrac e{e+1}v(S_1)+\tfrac1{e+1}v(S_2)\Bigr).$$
--   2. If $c_i/B\le\lambda<1$ for every $i$, then some $S\in E(p^v,c)$ has $\mathrm{OPT}\le e^{1/(1-\lambda)}\,v(S)$.
--   3. If $M/\mathrm{OPT}\le\theta<1$, then some $S\in E(p^v,c)$ has $\mathrm{OPT}\le\frac e{1-\theta}\,v(S)$.
--
--   So, unlike the price of anarchy, the price of stability of compensation design is a constant for monotone XOS valuations.
--
--   **Formalization Note** The singleton rule breaks ties by an injective agent priority $\rho$, fixed with the rule before the costs; the claim is made for every such $\rho$.
--
--   Differences from the source:
--   - generalization: there is a randomized payment rule (the singleton rule's tie-breaking unspecified) → for every injective agent priority ρ, the mixture whose singleton branch breaks ties by ρ; reason: an injective priority exists (the agent index), so the statement specializes to the existence claim
--   - encoding: a randomized payment rule (a distribution over budget-feasible deterministic rules, p.5) → both branches asserted IsCompRule B: nonnegative, zero outside S, budget feasible; reason: this is the definition of a compensation rule on p.5, made an explicit conjunct
--   - encoding: PoS(P, c) ≤ α, the ratio of OPT to the expected best-equilibrium value → existence of equilibria S₁ (marginal-contribution branch) and S₂ (singleton branch), resp. S, with OPT ≤ α·(weighted values); reason: the equilibrium sets are finite, so the best equilibrium is attained; the form also asserts the existence the paper assumes and avoids the ratio's division by zero
--   - encoding: M/OPT ≤ θ → M ≤ θ·OPT; reason: the same condition when OPT > 0; at OPT = 0 the claim OPT ≤ α·v(S) holds for any equilibrium S since v ≥ 0
--   - encoding: the asymptotic rewrites = e + o_λ(1), = e + o_θ(1) → omitted; reason: they restate the limit of the explicit bound as λ, θ → 0 and add no claim about the rule
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem 3.4, p.17 (PDF 19)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsXOS
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesignBFM_M
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_Supplement_IsPNEOf
import Definitions.Def_CompDesignBFM_Supplement_IsCompRule
import Definitions.Def_CompDesignBFM_Supplement_singletonPay

namespace CompDesignBFM

namespace Supplement

/-- Theorem 3.4 (constant PoS bounds for monotone XOS functions), Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.17, PDF 19. Let `v` be a
monotone XOS function and `B > 0`.
1. The randomized payment rule that runs the marginal-contribution rule `mcPay v B` with probability
   `e/(e+1)` and the singleton rule with probability `1/(e+1)` has PoS at most `e + 1`.
2. If `cᵢ/B ≤ λ < 1` for all `i`, the marginal-contribution rule has PoS at most `e^(1/(1−λ))`.
3. If `M/OPT ≤ θ < 1`, the marginal-contribution rule has PoS at most `e/(1−θ)`.
**Formalization Note.** Both branches are asserted to be compensation rules (nonnegative, zero outside
`S`, budget feasible), and the rule is fixed before the costs. "PoS ≤ α" is
`OPT ≤ α · E[best equilibrium value]`; as equilibrium sets are finite, this is the existence of
equilibria `S₁` (marginal-contribution branch) and `S₂` (singleton branch) with
`OPT ≤ (e+1)(e/(e+1) · v(S₁) + 1/(e+1) · v(S₂))`. The singleton rule breaks ties by an injective agent
priority `rho`; the claim is made for every such `rho`. `M/OPT ≤ θ` is written `M ≤ θ · OPT`. `e` is
`Real.exp 1`. -/
theorem theorem_3_4 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (hB : 0 < B)
    (hm : IsMonotoneSF v) (hxos : IsXOS v) (rho : Fin n → ℕ) (hrho : Function.Injective rho) :
    (IsCompRule B (mcPay v B) ∧ IsCompRule B (singletonPay v B rho)) ∧
    (∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) →
      ∃ S₁ S₂ : Finset (Fin n), IsPNE v B c S₁ ∧ IsPNEOf (singletonPay v B rho) c S₂ ∧
        OPT v B c ≤ (Real.exp 1 + 1) *
          (Real.exp 1 / (Real.exp 1 + 1) * v S₁ + 1 / (Real.exp 1 + 1) * v S₂)) ∧
    (∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → ∀ l : ℝ, l < 1 → (∀ i, c i / B ≤ l) →
      ∃ S : Finset (Fin n), IsPNE v B c S ∧ OPT v B c ≤ Real.exp (1 / (1 - l)) * v S) ∧
    (∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → ∀ θ : ℝ, θ < 1 → M v B c ≤ θ * OPT v B c →
      ∃ S : Finset (Fin n), IsPNE v B c S ∧ OPT v B c ≤ Real.exp 1 / (1 - θ) * v S) := by sorry

end Supplement

end CompDesignBFM
