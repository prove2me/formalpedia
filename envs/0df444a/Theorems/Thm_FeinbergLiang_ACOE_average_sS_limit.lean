-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_average_sS_limit
-- name    : FeinbergLiang.ACOE.average_sS_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:05:08.893368+00:00
-- url     : https://prove2.me/theorems/e19f72a4-09dd-4f85-9bc2-bb58db02c919
-- title:
--   Theorem 4.4 — limits of discount-optimal $(s'_\alpha,S'_\alpha)$ thresholds give an average-cost optimal $(s^*,S^*)$ policy satisfying the ACOI
-- statement:
--   Consider the inventory control problem. For each nonnegative $\alpha\in(\alpha^*,1)$, let $(s'_\alpha,S'_\alpha)$ with $s'_\alpha\le S'_\alpha$ be thresholds for which the $(s'_\alpha,S'_\alpha)$ policy is optimal for the discount factor $\alpha$. Let $\{\alpha_n\uparrow1\}$ be a sequence of nonnegative discount factors with $\alpha_1>\alpha^*$. Then:
--   1. the sequence $\{(s'_{\alpha_n},S'_{\alpha_n})\}$ is bounded;
--   2. suppose $(s^*,S^*)=\lim_{k\to\infty}(s'_{\alpha_{n_k}},S'_{\alpha_{n_k}})$ along a subsequence $\{\alpha_{n_k}\}$. Then $s^*\le S^*$, and the $(s^*,S^*)$ policy $\phi$ is average-cost optimal;
--   3. with $\tilde u$ defined in (2.5) for that subsequence, $w$ and $\tilde u$ are finite, and $\phi$ satisfies the average-cost optimality inequality
--   $$w+\tilde u(x)\ge c(x,\phi(x))+\int\tilde u(y)\,q(dy\mid x,\phi(x))=K I_{\{\phi(x)>0\}}+H(x+\phi(x))-\bar cx,\qquad x\in\mathbb R.$$
--
--   The paper cites this from Feinberg and Lewis (2015, Theorem 6.10(iii)).
--
--   **Formalization Note.** The paper says the policy "satisfies the optimality inequality (4.8)". Inequality (4.8) is the policy-free inequality $w+\tilde u(x)\ge\min\{\min_{a\ge0}[K+H(x+a)],H(x)\}-\bar cx$. The reading used here, and in the paper's proof of Theorem 4.5, is the inequality for the policy itself, which is the ACOI (3.1) and implies (4.8). It is stated in the general form $w+\tilde u(x)\ge c(x,\phi(x))+\int\tilde u\,dq$, after subtracting the cost's lower bound $0$. The paper indexes the sequence from $\alpha_1$, and Lean from `α 0`. A limit point is taken along a strictly increasing reindexing $\psi$.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, p. 578, Theorem 4.4 (citing Feinberg and Lewis 2015, Theorem 6.10(iii)), Eq. (4.8)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergLiang_ACOE_Inventory
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- Theorem 4.4 (Feinberg–Liang 2022, p. 578, citing Feinberg and Lewis 2015, Theorem 6.10(iii)).
Fix, for each nonnegative `α ∈ (α*, 1)`, an `α`-optimal `(s'_α, S'_α)` policy. For every
sequence `α_n ↑ 1` of nonnegative discount factors with `α_1 > α*` (Lean's `α 0`), the
thresholds `(s'_{α_n}, S'_{α_n})` are bounded, and every limit `(s*, S*)` along a subsequence
`α_{n_k}` defines an average-cost optimal `(s*, S*)` policy satisfying the optimality inequality
`w + ũ(x) ≥ c(x, ϕ(x)) + ∫ ũ(y) q(dy | x, ϕ(x))` with `ũ` of (2.5) for that subsequence
(and `w`, `ũ` finite). -/
theorem average_sS_limit (D : InventoryData) (s' S' : ℝ → ℝ)
    (hopt : ∀ β ∈ Set.Ico (0 : ℝ) 1, alphaStar D < (β : EReal) →
      s' β ≤ S' β ∧
      IsDiscOptimal (inventoryMDP D)
        (Policy.ofStationary (sSPolicy (s' β) (S' β)) (measurable_sSPolicy _ _)) β)
    (α : ℕ → ℝ) (hα : IsDiscountSeq α) (hα0 : alphaStar D < (α 0 : EReal)) :
    Bornology.IsBounded (Set.range fun n => (s' (α n), S' (α n))) ∧
    ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ sS : ℝ × ℝ,
      Tendsto (fun k => (s' (α (ψ k)), S' (α (ψ k)))) atTop (𝓝 sS) →
      sS.1 ≤ sS.2 ∧
      IsAvgOptimal (inventoryMDP D)
        (Policy.ofStationary (sSPolicy sS.1 sS.2) (measurable_sSPolicy _ _)) ∧
      wLower (inventoryMDP D) ≠ ⊤ ∧
      (∀ x, uTilde (inventoryMDP D) (α ∘ ψ) x ≠ ⊤) ∧
      ∀ x, (inventoryMDP D).cost x (sSPolicy sS.1 sS.2 x) +
          ∫⁻ y, uTilde (inventoryMDP D) (α ∘ ψ) y
            ∂((inventoryMDP D).q (x, sSPolicy sS.1 sS.2 x)) ≤
        wLower (inventoryMDP D) + uTilde (inventoryMDP D) (α ∘ ψ) x := by sorry

end FeinbergLiang.ACOE
