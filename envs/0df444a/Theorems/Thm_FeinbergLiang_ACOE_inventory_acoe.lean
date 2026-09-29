-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_inventory_acoe
-- name    : FeinbergLiang.ACOE.inventory_acoe
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:07:31.003706+00:00
-- url     : https://prove2.me/theorems/ca055319-c900-4b75-8c10-edc5716b5866
-- title:
--   Theorem 4.5 — the average-cost optimality equation holds for setup-cost inventory control, with K-convex ũ and H and optimal (s, S) policies
-- statement:
--   Consider the periodic-review inventory control problem with backorders, fixed ordering cost $K\ge0$, per-unit cost $\bar c>0$, and convex holding/backordering cost $h$ with $h(x)\to\infty$ as $|x|\to\infty$ (normalized so that $h\ge0$ and $h(0)=0$). Demands are i.i.d. and nonnegative, with $\mathbb E[h(x-D)]<\infty$ for all $x$ and $P(D>0)>0$. The state space is $\mathbb R$ and the action space is $[0,\infty)$. Let $\{\alpha_n\uparrow1\}$ be a sequence of nonnegative discount factors with $\alpha_1>\alpha^*$. Then the following hold.
--
--   1. The MDP satisfies Assumption EC for $\{\alpha_n\}$.
--   2. The conclusions of Theorem 3.2 hold. There is a subsequence $\{\alpha_{n_k}\}$ along which $u_{\alpha_{n_k}}\to\tilde u$ pointwise and uniformly on compact sets, where $\tilde u$ is defined in (2.5) for the subsequence and is finite. Moreover, $w=\underline w$ is finite, and $H(x)=\bar cx+\mathbb E[h(x-D)]+\mathbb E[\tilde u(x-D)]$ is finite for every $x$.
--   3. There is a stationary policy $\phi$ such that for all $x\in\mathbb R$
--   $$w+\tilde u(x)=K I_{\{\phi(x)>0\}}+H(x+\phi(x))-\bar cx=\min\Big\{\min_{a\ge0}[K+H(x+a)],\,H(x)\Big\}-\bar cx,\qquad(4.10)$$
--   and every stationary policy satisfying (4.10) is average-cost optimal.
--   4. The functions $\tilde u$ and $H$ are $K$-convex, continuous and inf-compact.
--   5. $H$ has a minimizer. For every minimizer $S$ (4.5), with $s=\inf\{x\le S: H(x)\le K+H(S)\}$ (4.6), the set in (4.6) is bounded below, $s\le S$, and the $(s,S)$ policy satisfies (4.10).
--   6. Suppose that for each nonnegative $\alpha\in(\alpha^*,1)$ an $(s'_\alpha,S'_\alpha)$ policy is optimal for the discount factor $\alpha$, with $s'_\alpha\le S'_\alpha$. Then along some further subsequence of $\{\alpha_{n_k}\}$ the thresholds converge. For every further subsequence along which they converge to some $(s^*,S^*)$, we have $s^*\le S^*$, and the $(s^*,S^*)$ policy satisfies (4.10).
--
--   This is the paper's main result. It verifies the ACOE for the classical inventory problem with setup costs and general demand distributions. It shows that the average-cost relative value function is $K$-convex and continuous, and that optimal $(s,S)$ policies can be read off directly from the ACOE.
--
--   **Formalization Note.** Only case (i), $\mathbb X=\mathbb R$, $\mathbb A=\mathbb R^+$, is formalized. Case (ii), $\mathbb X=\mathbb Z$, $\mathbb A=\mathbb N_0$, is not.
--   1. The hypotheses $h\ge0$ and $h(0)=0$ are the paper's own "without loss of generality" assumption.
--   2. The paper's $\alpha_1$ is Lean's `α 0`, and "$\alpha_n\uparrow1$" means values in $[0,1)$, nondecreasing, with limit $1$.
--   3. $H$ is extended-real valued by definition, and its finiteness is concluded.
--   4. "$=\min\{\dots\}$" in (4.10) is read as: the middle expression is $\le K+H(x+a)-\bar cx$ for every $a\ge0$ and $\le H(x)-\bar cx$.
--   5. The paper's $\tilde u$ is the one "defined in (2.5) for the subsequence" of Theorem 3.2(i), so the subsequence is existential and $\tilde u$ depends on it.
--   6. The paper's "can be selected as an $(s^*,S^*)$ policy described in Theorem 4.4" is formalized with the convergence taken along further subsequences of that subsequence, as in the paper's proof.
--   7. "Can also be selected as an $(s,S)$ policy" is formalized for every minimizer $S$ of $H$.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, p. 578, Theorem 4.5, Eqs. (4.9), (4.10)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_FeinbergLiang_ACOE_Inventory
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- Theorem 4.5 (Feinberg–Liang 2022, p. 578), case `X = ℝ`, `A = ℝ⁺`. For each sequence
`α_n ↑ 1` of nonnegative discount factors with `α_1 > α*` (Lean's `α 0`):
the inventory MDP satisfies Assumption EC; along a subsequence `α_{n_k}` the conclusions of
Theorem 3.2 hold with `ũ` of (2.5) for that subsequence; there is a stationary policy satisfying
(4.10), and every stationary policy satisfying (4.10) is average-cost optimal; `ũ` and `H` of
(4.9) are `K`-convex, continuous and inf-compact; an `(s, S)` policy with `S` a minimizer of
`H` (4.5) and `s` from (4.6) satisfies (4.10); and the limits `(s*, S*)` of discount-optimal
thresholds along further subsequences (Theorem 4.4) exist and define policies satisfying (4.10). -/
theorem inventory_acoe (D : InventoryData) (α : ℕ → ℝ) (hα : IsDiscountSeq α)
    (hα0 : alphaStar D < (α 0 : EReal)) :
    AssumptionEC (inventoryMDP D) α ∧
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      let ũ := uTilde (inventoryMDP D) (α ∘ ψ)
      -- conclusions of Theorem 3.2(i)
      (∀ x, ũ x ≠ ⊤) ∧
      (∀ x, Tendsto (fun k => uRel (inventoryMDP D) (α (ψ k)) x) atTop (𝓝 (ũ x))) ∧
      (∀ C : Set ℝ, IsCompact C →
        TendstoUniformlyOn (fun k x => (uRel (inventoryMDP D) (α (ψ k)) x).toReal)
          (fun x => (ũ x).toReal) atTop C) ∧
      -- finiteness of w and H, so that (4.10) is an identity of real numbers
      wLower (inventoryMDP D) ≠ ⊤ ∧
      (∀ x, Hfun D ũ x ≠ ⊤) ∧
      -- (4.10) and optimality
      (∃ ϕ : ℝ → ℝ≥0, Measurable ϕ ∧ ∀ x, InvACOE D ũ ϕ x) ∧
      (∀ (ϕ : ℝ → ℝ≥0) (hϕ : Measurable ϕ), (∀ x, InvACOE D ũ ϕ x) →
        IsAvgOptimal (inventoryMDP D) (Policy.ofStationary ϕ hϕ)) ∧
      -- ũ and H are K-convex, continuous and inf-compact
      KConvex D.K (fun x => (ũ x).toReal) ∧ Continuous (fun x => (ũ x).toReal) ∧
      InfCompact (fun x => (ũ x).toReal) ∧
      KConvex D.K (fun x => (Hfun D ũ x).toReal) ∧ Continuous (fun x => (Hfun D ũ x).toReal) ∧
      InfCompact (fun x => (Hfun D ũ x).toReal) ∧
      -- the (s, S) policy from (4.5)–(4.6) for f = H
      (∃ S : ℝ, ∀ x, Hfun D ũ S ≤ Hfun D ũ x) ∧
      (∀ S : ℝ, (∀ x, Hfun D ũ S ≤ Hfun D ũ x) →
        BddBelow {x : ℝ | x ≤ S ∧ Hfun D ũ x ≤ (D.K : EReal) + Hfun D ũ S} ∧
        lowerThreshold (Hfun D ũ) D.K S ≤ S ∧
        ∀ x, InvACOE D ũ (sSPolicy (lowerThreshold (Hfun D ũ) D.K S) S) x) ∧
      -- the (s*, S*) policy of Theorem 4.4
      ∀ s' S' : ℝ → ℝ,
        (∀ β ∈ Set.Ico (0 : ℝ) 1, alphaStar D < (β : EReal) →
          s' β ≤ S' β ∧
          IsDiscOptimal (inventoryMDP D)
            (Policy.ofStationary (sSPolicy (s' β) (S' β)) (measurable_sSPolicy _ _)) β) →
        (∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ ∃ sS : ℝ × ℝ,
          Tendsto (fun k => (s' (α (ψ (ψ' k))), S' (α (ψ (ψ' k))))) atTop (𝓝 sS)) ∧
        ∀ ψ' : ℕ → ℕ, StrictMono ψ' → ∀ sS : ℝ × ℝ,
          Tendsto (fun k => (s' (α (ψ (ψ' k))), S' (α (ψ (ψ' k))))) atTop (𝓝 sS) →
          sS.1 ≤ sS.2 ∧ ∀ x, InvACOE D ũ (sSPolicy sS.1 sS.2) x := by sorry

end FeinbergLiang.ACOE
