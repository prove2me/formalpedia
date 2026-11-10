-- Prove2me | Theorems.Thm_BilatMatch_lemma_3_4
-- name    : BilatMatch.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:33.696387+00:00
-- url     : https://prove2.me/theorems/8404431b-f548-4d4c-acdc-601fb4d3224e
-- title:
--   Lemma 3.4 (Bilateral Value in Terms of Trade Masses) — $F_S(\kappa)V_\alpha(F_B,F^\kappa_S)=\max_{\mu\in P(F_S(\kappa))}\sum_\ell f_B(v_\ell)L_{\alpha,\ell}(\mu)$
-- statement:
--   Fix $\alpha\ge0$ and an $\alpha$-weakly regular seller prior $F_S$ (finite or regular with interval support). For every positive-mass initial cap $\kappa$ and every buyer prior $F_B$ with support $\{v_1<\dots<v_n\}$,
--   $$F_S(\kappa)\,V_\alpha(F_B,F^\kappa_S)=\max_{\mu\in P(F_S(\kappa))}\sum_\ell f_B(v_\ell)L_{\alpha,\ell}(\mu),$$
--   where $F^\kappa_S$ is the seller prior conditioned on $\kappa$, and the maximum is attained.
--
--   The identity expresses the bilateral Lagrangian value under every cap through one cost function $C_\alpha$ of the full seller prior, which is what allows rules for different caps to be compared.
--
--   **Formalization Note** $V_\alpha(F_B,F^\kappa_S)$ is the bilateral value with whole-line reports.
--
--   Differences from the source:
--   - reading: bilateral V_α (the optimal bilateral Lagrangian, p.10) → bilateral V_α with BIC/IIR at every real type and report; reason: the paper's mechanisms are built with whole-line BIC/IIR (eq. (1), Lemma B.4); for finite priors the support-restricted and whole-line values coincide (Lemma B.4(i)), so the hypothesis is unchanged and the conclusion takes the stronger reading
--   - encoding: buyer prior F_B with support {v_1, …, v_n} → ∑_ℓ w_ℓ δ_{v_ℓ} with v strictly increasing, all w_ℓ > 0, ∑ w_ℓ = 1; reason: same objects; indices start at 0
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma 3.4, eq. (7), p.11 (pdf p.13)

import Mathlib
import Definitions.Def_BilatMatch_sellerCost
import Definitions.Def_BilatMatch_massLagrangian
import Definitions.Def_BilatMatch_typewise
import Definitions.Def_BilatMatch_ValphaOn

open MeasureTheory

namespace BilatMatch

/-- **Lemma 3.4 (Bilateral Value in Terms of Trade Masses).** Liu, Qin, Wang, arXiv:2609.30702
(held version, sha256 ff1490ad…), Lemma 3.4, eq. (7), p.11 (pdf p.13); standing assumptions of
§3.2, p.10.

Let `F_S` be `α`-weakly regular (`α ≥ 0`), finite or regular with interval support. For every
positive-mass initial cap `κ` and every buyer prior `F_B` with support `{v_1 < ⋯ < v_n}`,
`F_S(κ) V_α(F_B, F^κ_S) = max_{µ ∈ P(F_S(κ))} ∑_ℓ f_B(v_ℓ) L_{α,ℓ}(µ)`, the maximum being attained.

**Formalization Note** `F^κ_S` is `ProbabilityTheory.cond F κ`. `F_B` is `∑_ℓ w_ℓ δ_{v_ℓ}` with
`w_ℓ > 0`, `∑ w_ℓ = 1`; indices start at `0`. `L_{α,ℓ}` uses `C_α` of the full seller prior.
`V_α(F_B, F^κ_S)` is the bilateral mechanism value with whole-line reports. -/
theorem lemma_3_4 (α : ℝ) (hα : 0 ≤ α) (F : Measure ℝ) (DS : Set ℝ) (τα : ℝ → ℝ)
    (hF : IsAlphaWeaklyRegular α F DS τα) (κ : Set ℝ) (hκ : IsCap DS κ) (hpos : 0 < F κ)
    {n : ℕ} (v : Fin n → ℝ) (hv : StrictMono v) (w : Fin n → ℝ) (hw : ∀ ℓ, 0 < w ℓ)
    (hw1 : ∑ ℓ, w ℓ = 1) :
    ∃ m ∈ massPolytope n (F κ).toReal,
      (∀ m' ∈ massPolytope n (F κ).toReal,
        ∑ ℓ, w ℓ * massLagrangian α v (sellerCost F τα) m' ℓ ≤
          ∑ ℓ, w ℓ * massLagrangian α v (sellerCost F τα) m ℓ) ∧
      ((F κ).toReal : EReal) * Valpha (bilateral (finiteLaw v w) (ProbabilityTheory.cond F κ)) α =
        ((∑ ℓ, w ℓ * massLagrangian α v (sellerCost F τα) m ℓ : ℝ) : EReal) := by sorry

end BilatMatch
