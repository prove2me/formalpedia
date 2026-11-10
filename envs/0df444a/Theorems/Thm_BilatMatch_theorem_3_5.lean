-- Prove2me | Theorems.Thm_BilatMatch_theorem_3_5
-- name    : BilatMatch.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:33.951376+00:00
-- url     : https://prove2.me/theorems/85978178-6321-4ec2-a432-be1141f1e8be
-- title:
--   Theorem 3.5 (Cap-Compatible Bilateral Rules) — bilateral bounds yield a cap-compatible family with $\ell^\kappa_\alpha(v;z^\kappa)\ge\beta\int_\kappa(v-c)_+dF_S$
-- statement:
--   Fix $\alpha\ge0$, an $\alpha$-weakly regular seller prior $F_S$ (finite or regular with interval support), buyer values $v_1<\dots<v_n$ and $\beta\ge0$. If
--   $$V_\alpha(F_B,F^\kappa_S)\ \ge\ \beta\,\mathrm{FB}(F_B,F^\kappa_S)$$
--   for every buyer prior $F_B$ on $\{v_1,\dots,v_n\}$ and every positive-mass cap $\kappa$, then there is a cap-compatible family $z^\kappa$ such that
--   $$\ell^\kappa_\alpha(v;z^\kappa)\ \ge\ \beta\int_\kappa(v-c)_+\,dF_S(c)$$
--   for every cap $\kappa$ and every buyer type $v$ in the support.
--
--   This strengthens a bilateral average guarantee to a typewise guarantee, chosen monotonically across caps, which is exactly the input of Theorem 3.2.
--
--   **Formalization Note** Buyer priors on the fixed support have strictly positive weights. Caps are initial sets of the seller's report domain. The bilateral values use whole-line reports.
--
--   Differences from the source:
--   - reading: bilateral V_α(F_B, F^κ_S) → bilateral V_α with BIC/IIR at every real type and report; reason: the paper's mechanisms are built with whole-line BIC/IIR (eq. (1), Lemma B.4); for finite priors the support-restricted and whole-line values coincide (Lemma B.4(i)), so the hypothesis is unchanged and the conclusion takes the stronger reading
--   - encoding: every buyer prior on the fixed support → ∑_ℓ w_ℓ δ_{v_ℓ} with all w_ℓ > 0, ∑ w_ℓ = 1; reason: the priors with exactly this support
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Theorem 3.5, p.12 (pdf p.14)

import Mathlib
import Definitions.Def_BilatMatch_sellerCost
import Definitions.Def_BilatMatch_massLagrangian
import Definitions.Def_BilatMatch_typewise
import Definitions.Def_BilatMatch_ValphaOn
import Definitions.Def_BilatMatch_FB

open MeasureTheory

namespace BilatMatch

/-- **Theorem 3.5 (Cap-Compatible Bilateral Rules).** Liu, Qin, Wang, arXiv:2609.30702 (held
version, sha256 ff1490ad…), Theorem 3.5, p.12 (pdf p.14); standing assumptions of §3.2, p.10.

Let `α ≥ 0`, `F_S` `α`-weakly regular (finite or regular with interval support), and fix buyer
values `v_1 < ⋯ < v_n`. Fix `β ≥ 0`. If `V_α(F_B, F^κ_S) ≥ β FB(F_B, F^κ_S)` for every buyer prior on
this support and every positive-mass cap `κ`, then there is a cap-compatible family `z^κ` with
`ℓ^κ_α(v; z^κ) ≥ β ∫_κ (v − c)_+ dF_S(c)` for every cap `κ` and every buyer type `v` in the support.

**Formalization Note** Buyer priors on the fixed support are `∑_ℓ w_ℓ δ_{v_ℓ}` with all `w_ℓ > 0`.
Caps are initial sets of the seller report domain `DS` (the support, or `[c̲, c̄]`), possibly empty,
open or closed. The buyer domain of the family is `{v_1, …, v_n}`; `ℓ^κ_α` is eq. (5) with the
discrete buyer rent and the full seller prior. -/
theorem theorem_3_5 (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (F : Measure ℝ) (DS : Set ℝ)
    (τα : ℝ → ℝ) (hF : IsAlphaWeaklyRegular α F DS τα) {n : ℕ} (v : Fin n → ℝ)
    (hv : StrictMono v)
    (hbil : ∀ w : Fin n → ℝ, (∀ ℓ, 0 < w ℓ) → ∑ ℓ, w ℓ = 1 → ∀ κ : Set ℝ, IsCap DS κ →
      0 < F κ →
      ((β * (FB (bilateral (finiteLaw v w) (ProbabilityTheory.cond F κ))).toReal : ℝ) : EReal) ≤
        Valpha (bilateral (finiteLaw v w) (ProbabilityTheory.cond F κ)) α) :
    ∃ z : Set ℝ → ℝ → ℝ → ℝ, IsCapCompatible (Set.range v) DS z ∧
      ∀ κ : Set ℝ, IsCap DS κ → ∀ ℓ : Fin n,
        β * ∫ c in κ, max (v ℓ - c) 0 ∂F ≤ typewise α (Set.range v) DS F (z κ) (v ℓ) := by sorry

end BilatMatch
