-- Prove2me | Theorems.Thm_FeedbackSwitching_corollary_2
-- name    : FeedbackSwitching.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:59.621354+00:00
-- url     : https://prove2.me/theorems/7c73ef06-ca0f-45b4-8abf-5f4e91f30834
-- title:
--   Corollary 2 — block loss $\le p^{\mathsf T}L-\beta\Gamma+\beta\delta h^3$ and $\mathbb EN_{\rm int}\le\frac{13}8\mu h$
-- statement:
--   Let $(p,x)$ be a holding family, $\kappa=2^{-m}$ with an integer $m\ge5$, $\kappa\lambda_{\max}\le1/4$, and $h\ge1$ an integer with $h\kappa\le1/8$. Let $0<\delta<1$ and $M\ge100\log(2/\delta)$, $\beta=1/(4M)$. Suppose the scores form a score rule for every $P_\tau$, $\tau\in[\kappa,1]$, and that each $\Psi_s\ell$ ($\ell\in[0,1]^K$) is computable from the comparisons revealed by $s$. For deterministic $\ell_1,\dots,\ell_h\in[0,1]^K$ with sum $L$, the block procedure (lines 5–8 of Algorithm 1) is causal and observable, and its actions and internal switch count $N_{\rm int}=\sum_{t=1}^{h-1}\mathbf 1\{X_{t+1}\ne X_t\}$ satisfy, with $\mu=\kappa(1+m/2)$,
--   $$
--   \mathbb E\sum_{t=1}^{h}\ell_t(X_t)\le p^{\mathsf T}L-\beta\,\Gamma(\ell_{1:h})+\beta\delta h^3,\qquad\mathbb EN_{\rm int}\le\tfrac{13}{8}\mu h .
--   $$
--   Steering lowers the expected loss of a block by $\beta$ times the steering gain, at a switching cost of order $\mu h$.
--
--   **Formalization Note** "Causal and observable" is stated as: with the same coins, two loss blocks with the same comparisons at the actions played before round $t$ give the same action in round $t$, and the same raw estimate $Z$ when the comparisons agree on all rounds. The expectations are over i.i.d. uniform coins and are asserted to be of integrable functions.
--
--   Differences from the source:
--   - generalization: a fixed tournament orientation defines the comparisons → any relation A defines the comparisons (N⁺(s) = {s} ∪ {j : A s j}); the score-rule and Ψ hypotheses and the causality clause all refer to the same A; reason: the proof uses the comparisons only for causality and observability, which are stated relative to A; taking A the selected tournament gives the paper's statement
--   - encoding: the block procedure's random draws; E → the procedure on i.i.d. uniform coins (one for τ, one per boundary, one per round), expectations as integrals asserted integrable; reason: each draw has the law the pseudocode states (inverse CDF); same instances
--   - encoding: causal and observable (p.15) → equality of the actions and of Z for loss blocks with the same comparisons at the played actions, under the same coins; reason: each action depends only on past comparisons and private randomness; this is that property for a deterministic loss block
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Corollary 2, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_FeedbackSwitching_blockRun
import Definitions.Def_FeedbackSwitching_tScore
import Definitions.Def_FeedbackSwitching_steeringGain
open MeasureTheory Matrix

namespace FeedbackSwitching

/-- **Corollary 2 (Block loss and switches)**, p.30 (PDF p.32). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

Let `(p, x)` be a holding family, `κ = 2^{−m}` with an integer `m ≥ 5`, `κλ_max ≤ 1/4`, and `h ≥ 1`
an integer with `hκ ≤ 1/8`. Let `0 < δ < 1` and `M ≥ 100 log(2/δ)`. Suppose the scores form a
score rule for every `P_τ` with `τ ∈ [κ, 1]`, and that the estimation matrices `(Ψ_s)`, known at the
start of the block, have `Ψ_s ℓ` computable from the comparisons revealed by `s` for every
`ℓ ∈ [0,1]^K`. For deterministic `ℓ_1, …, ℓ_h ∈ [0,1]^K` with sum `L`, the block procedure in lines
5 to 8 of Algorithm 1 is causal and observable, and its actions `X_1, …, X_h` and internal switch
count `N_int = ∑_{t=1}^{h−1} 1{X_{t+1} ≠ X_t}` satisfy, with `µ = κ(1 + m/2)` and `β = 1/(4M)`,
`E ∑_{t=1}^h ℓ_t(X_t) ≤ pᵀL − βΓ(ℓ_{1:h}) + βδh³` and `E N_int ≤ (13/8)µh`.

**Formalization Note.** The procedure is `blockRun B` on i.i.d. uniform coins (`coinLaw`), with
`B.p = p`, `B.x = x`, `B.Ψ = (Ψ_s)`, `B.m = m`, `B.M = M` and `B.d τ` the scores for `P_τ`; it reads
the loss vector `ℓ_t` of the round. Rounds are 0-based. "Causal and observable" (p.15) is the first
two clauses: with the same coins, the action of round `t` is the same for any two loss blocks with
the same comparisons at the actions played before `t`, and the raw estimate `Z` is the same when
the comparisons agree on all rounds. The expectations are asserted to be of integrable functions. -/
theorem corollary_2 {K : ℕ} [NeZero K] (A : Fin K → Fin K → Prop) (B : BlockInput K)
    (hpx : IsHoldingPair B.p B.x) (hm : 5 ≤ B.m)
    (hlam : ∀ s, baseRate B.m * lam B.p B.x s ≤ 1 / 4)
    (h : ℕ) (hh : 1 ≤ h) (hhκ : (h : ℝ) * baseRate B.m ≤ 1 / 8)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hM : 100 * Real.log (2 / δ) ≤ B.M)
    (hscore : ∀ τ, baseRate B.m ≤ τ → τ ≤ 1 → IsScoreRule A (holdingP B.p B.x τ) B.p (B.d τ))
    (hΨ : ∀ s ℓ ℓ', InUnitCube ℓ → InUnitCube ℓ' → sameComparisons A s ℓ ℓ' →
      B.Ψ s *ᵥ ℓ = B.Ψ s *ᵥ ℓ')
    (ℓ : ℕ → Fin K → ℝ) (hℓ : ∀ t < h, InUnitCube (ℓ t)) :
    (∀ ℓ' : ℕ → Fin K → ℝ, (∀ t < h, InUnitCube (ℓ' t)) → ∀ (ω : Coins) (t : ℕ), t < h →
      (∀ t' < t, sameComparisons A (blockRun B (fun r _ => ℓ r) ω t').X (ℓ t') (ℓ' t')) →
        (blockRun B (fun r _ => ℓ' r) ω t).X = (blockRun B (fun r _ => ℓ r) ω t).X) ∧
    (∀ ℓ' : ℕ → Fin K → ℝ, (∀ t < h, InUnitCube (ℓ' t)) → ∀ ω : Coins,
      (∀ t' < h, sameComparisons A (blockRun B (fun r _ => ℓ r) ω t').X (ℓ t') (ℓ' t')) →
        blockZ B (fun r _ => ℓ' r) h ω = blockZ B (fun r _ => ℓ r) h ω) ∧
    Integrable (fun ω => ∑ t ∈ Finset.range h, ℓ t (blockRun B (fun r _ => ℓ r) ω t).X) coinLaw ∧
    ∫ ω, ∑ t ∈ Finset.range h, ℓ t (blockRun B (fun r _ => ℓ r) ω t).X ∂coinLaw
      ≤ B.p ⬝ᵥ (∑ t ∈ Finset.range h, ℓ t) - 1 / (4 * B.M) * steeringGain B.p B.x B.m ℓ h
        + 1 / (4 * B.M) * δ * (h : ℝ) ^ 3 ∧
    Integrable (fun ω => internalSwitches (fun t => (blockRun B (fun r _ => ℓ r) ω t).X) h)
      coinLaw ∧
    ∫ ω, internalSwitches (fun t => (blockRun B (fun r _ => ℓ r) ω t).X) h ∂coinLaw
      ≤ 13 / 8 * meanRate B.m * h := by sorry

end FeedbackSwitching
