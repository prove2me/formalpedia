-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_considered_prob_ge_four_ninths
-- name    : CHMSPricing.UnitDemand.considered_prob_ge_four_ninths
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:16:08.482305+00:00
-- url     : https://prove2.me/theorems/70f7df87-197c-4725-8acf-387db341340a
-- title:
--   App. D.4, p. 20 — the claim $c_i \ge 4/9$: with probability at least $4/9$ agent $i$ is never blocked in either partition matroid
-- statement:
--   Consider single-parameter agents with independent values $v_{i'} \sim F_{i'}$ and prices $p_{i'}$; agent $i'$ desires service when $p_{i'} \le v_{i'}$, which happens with probability $q_{i'} = 1 - F_{i'}(p_{i'})$. Let $\mathcal M_1, \mathcal M_2$ be two partition matroids on the agents, with parts labelled by $\mathrm{part}_1, \mathrm{part}_2$ and capacities $\mathrm{cap}_1, \mathrm{cap}_2$. Suppose that in every part $P$ of either matroid
--   $$\sum_{i' \in P} q_{i'} \le \frac{\mathrm{cap}(P)}{3}.$$
--   Fix an agent $i$, lying in the part $P_1$ of $\mathcal M_1$ and the part $P_2$ of $\mathcal M_2$, with capacities $k_1 = \mathrm{cap}_1(P_1) \ge 1$ and $k_2 = \mathrm{cap}_2(P_2) \ge 1$. Let $\mathcal E_j$ be the event that at most $k_j - 1$ agents of $P_j$ other than $i$ desire service ($j = 1, 2$). Then
--   $$\Pr[\mathcal E_1 \cap \mathcal E_2] \ge \frac49.$$
--
--   On $\mathcal E_1 \cap \mathcal E_2$ agent $i$ is always considered for service, whatever the order, so this is the bound $c_i \ge 4/9$ that gives the factor $6.75 = 1/\big(\tfrac49\cdot\tfrac13\big)$ in Theorem 13.
--
--   **Formalization Note** The page counts in $\mathcal E_j$ the agents of $P_j$ desiring service, without excluding $i$; the formalization counts the agents other than $i$, which is the event under which $i$ is always considered and which is independent of $v_i$. The capacity $\mathrm{cap}(P)$ is used in place of the paper's $k_j$ (the largest number of elements of $P_j$ in an independent set); when $\mathrm{cap}(P_j) > |P_j|$ the event $\mathcal E_j$ is certain. The hypotheses $k_1, k_2 \ge 1$ are those of the paper's setting, where an agent of a part of capacity $0$ is never served.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 20, App. D.4, proof of Theorem 13 (the claim $c_i \ge 4/9$ and the events $\mathcal E_1, \mathcal E_2$)

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_ValueDist
import Definitions.Def_CHMSPricing_UnitDemand_SetSystem

namespace CHMSPricing.UnitDemand

/-- App. D.4, proof of Theorem 13, p. 20: the claim `cᵢ ≥ 4/9`. Two partition matroids on the
agents: agent `i` lies in part `P₁ = part₁⁻¹(part₁ i)` with capacity `k₁ = cap₁ (part₁ i) ≥ 1`
and in part `P₂ = part₂⁻¹(part₂ i)` with capacity `k₂ = cap₂ (part₂ i) ≥ 1`. If in every part
of either matroid the expected number of agents desiring service (`qᵢ = 1 − Fᵢ(pᵢ)`) is at most
a third of the part's capacity, then with probability at least `4/9` at most `k₁ − 1` agents of
`P₁` other than `i` and at most `k₂ − 1` agents of `P₂` other than `i` desire service — the
event `𝓔₁ ∩ 𝓔₂` under which `i` is always considered for service. -/
theorem considered_prob_ge_four_ninths {ι β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β₁] [DecidableEq β₂]
    (D : ι → ValueDist) (part₁ : ι → β₁) (cap₁ : β₁ → ℕ) (part₂ : ι → β₂) (cap₂ : β₂ → ℕ)
    (p : ι → ℝ)
    (hq₁ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₁ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₁ b : ℝ) / 3)
    (hq₂ : ∀ b, ∑ i' ∈ Finset.univ.filter (fun i' => part₂ i' = b), (1 - (D i').cdf (p i'))
      ≤ (cap₂ b : ℝ) / 3)
    (i : ι) (hk₁ : 1 ≤ cap₁ (part₁ i)) (hk₂ : 1 ≤ cap₂ (part₂ i)) :
    (4 / 9 : ℝ) ≤ (prior D {v |
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₁ i' = part₁ i)).card ≤ cap₁ (part₁ i) - 1 ∧
      ((desiring p v).filter (fun i' => i' ≠ i ∧ part₂ i' = part₂ i)).card ≤ cap₂ (part₂ i) - 1}).toReal := by sorry

end CHMSPricing.UnitDemand
