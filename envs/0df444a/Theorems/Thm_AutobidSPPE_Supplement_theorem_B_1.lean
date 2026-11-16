-- Prove2me | Theorems.Thm_AutobidSPPE_Supplement_theorem_B_1
-- name    : AutobidSPPE.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:07:56.753948+00:00
-- url     : https://prove2.me/theorems/a9fbc97a-9411-488f-8789-19615a4c9ac6
-- title:
--   Theorem B.1 — an a priori lower bound on equilibrium strategies
-- statement:
--   Consider a second-price auction with $n\ge1$ bidders, budgets $\rho_i>0$, and integrable valuations $v_i$ with an arbitrary joint law. Let
--   $$
--   M_i=\mathbb E[v_i^+]\in(0,\infty),\qquad v_i^+=\max\{v_i,0\}.
--   $$
--   Consider either mechanism:
--   1. **SPPE**: bidder $i$ bids $\alpha_iv_i$ with $\alpha_i\in[0,1]$, the highest bid wins (a tie rule picks among the highest) and pays the highest competing bid;
--   2. **SPTE**: bidder $i$ participates with probability $\alpha_i\in[0,1]$, independently of the valuations and of the other bidders, and bids $v_i$; the highest participating value wins and pays the highest value of the other participants ($0$ if none).
--
--   Let $s_i(\alpha)$ be bidder $i$'s expected payment. Every $\alpha\in[0,1]^n$ with
--   $$
--   s_i(\alpha)\le\rho_i,\qquad (1-\alpha_i)(\rho_i-s_i(\alpha))=0\qquad(i\in[n])
--   $$
--   satisfies $\alpha_i\ge c_i:=\min\{1,\rho_i/M_i\}$ for every $i$. Consequently $C_0:=\min_ic_i=\min\{1,\min_i\rho_i/M_i\}>0$, every such $\alpha$ lies in $[C_0,1]^n$, and for every $C\in(0,C_0]$ it lies in $[C,1]^n$.
--
--   This justifies restricting strategies to $[C,1]^n$ (Assumption 1.3) without excluding any equilibrium.
--
--   **Formalization Note** The SPPE payment uses the published `AutobidSPPE.alloc` and `AutobidSPPE.highestOther`; the SPTE payment is the expected throttling spending under the given law.
--
--   Differences from the source:
--   - generalization: every equilibrium α* satisfying budget feasibility and the no-unnecessary-pacing/throttling condition → every α ∈ [0,1]^n satisfying s_i(α) ≤ ρ_i and (1 − α_i)(ρ_i − s_i(α)) = 0 for all i; reason: the theorem and its proof use only these two conditions; equilibria satisfying them are a special case
--   - reading: a second-price auction (tie rule unspecified) → every deterministic single-winner tie rule, in both mechanisms; reason: the paper names no rule; the claim holds for each
--   - encoding: n bidders → 1 ≤ n; reason: C_0 is a minimum over the bidders, defined only for n ≥ 1
--   - encoding: participation coins independent of the valuation profile → the finite sum over participation sets weighted by ∏ α_j ∏ (1 − α_k) (spendT); reason: the expectation over independent Bernoulli coins
--   - generalization: independent values v_i ∼ D_i (the model of Problems 1.1–1.2, p.4) → an arbitrary probability measure μ on value profiles with integrable coordinates; reason: Theorem B.1 assumes only integrable valuations and its proof (87) never uses independence of the values; independent laws are a special case
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem B.1, p.54

import Mathlib
import Definitions.Def_AutobidSPPE_alloc
import Definitions.Def_AutobidSPPE_highestOther
import Definitions.Def_AutobidSPPE_Supplement_spendT
open MeasureTheory

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- Theorem B.1, p.54 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), an a priori lower bound on equilibrium strategies. Consider a second-price auction
with `n ≥ 1` bidders, budgets `ρᵢ > 0`, and integrable valuations `vᵢ` with an arbitrary joint law `μ`; let
`Mᵢ = E[vᵢ⁺] ∈ (0, ∞)`. For either mechanism — SPPE (bidder `i` bids `αᵢvᵢ`) or SPTE (bidder `i` participates
with probability `αᵢ`, independently of the values, and bids `vᵢ`) — with `sᵢ(α)` bidder `i`'s expected payment,
every `α ∈ [0,1]ⁿ` with `sᵢ(α) ≤ ρᵢ` and `(1 − αᵢ)(ρᵢ − sᵢ(α)) = 0` for every `i` satisfies
`αᵢ ≥ cᵢ = min{1, ρᵢ/Mᵢ}` for every `i`. Consequently `C₀ = minᵢ cᵢ = min{1, minᵢ ρᵢ/Mᵢ} > 0`, every such `α`
belongs to `[C₀, 1]ⁿ`, and to `[C, 1]ⁿ` for every `C ∈ (0, C₀]`.

**Formalization Note** The SPPE payment is the published `alloc`/`highestOther` (winner by tie rule among the
highest bids, pays the highest competing bid); the SPTE payment is `spendT` with the law `μ`. Both
mechanisms allow every tie rule. -/
theorem theorem_B_1 {n : ℕ} (hn : 1 ≤ n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hint : ∀ i, Integrable (fun v : Fin n → ℝ => v i) μ) (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hM : ∀ i, 0 < ∫ v, max (v i) 0 ∂μ) (tie : TieRule n) :
    let M : Fin n → ℝ := fun i => ∫ v, max (v i) 0 ∂μ
    let c : Fin n → ℝ := fun i => min 1 (ρ i / M i)
    let C0 : ℝ := ⨅ i, c i
    let sP : (Fin n → ℝ) → Fin n → ℝ := fun α i => ∫ v, alloc tie α v i * highestOther α v i ∂μ
    let sT : (Fin n → ℝ) → Fin n → ℝ := fun α i => spendT μ tie α i
    0 < C0 ∧ C0 = min 1 (⨅ i, ρ i / M i) ∧
    (∀ α : Fin n → ℝ, (∀ i, α i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, sP α i ≤ ρ i ∧ (1 - α i) * (ρ i - sP α i) = 0) →
      (∀ i, c i ≤ α i) ∧ (∀ i, α i ∈ Set.Icc C0 1) ∧
      ∀ C : ℝ, 0 < C → C ≤ C0 → ∀ i, α i ∈ Set.Icc C 1) ∧
    (∀ α : Fin n → ℝ, (∀ i, α i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, sT α i ≤ ρ i ∧ (1 - α i) * (ρ i - sT α i) = 0) →
      (∀ i, c i ≤ α i) ∧ (∀ i, α i ∈ Set.Icc C0 1) ∧
      ∀ C : ℝ, 0 < C → C ≤ C0 → ∀ i, α i ∈ Set.Icc C 1) := by sorry

end AutobidSPPE.Supplement
