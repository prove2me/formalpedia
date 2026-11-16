-- Prove2me | Theorems.Thm_AutobidSPPE_Supplement_theorem_3_16
-- name    : AutobidSPPE.Supplement.theorem_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:04:26.345189+00:00
-- url     : https://prove2.me/theorems/82ef51f1-d537-4b3b-a187-3441587108d3
-- title:
--   Theorem 3.16 — second stage: geometric last-iterate convergence (throttling)
-- statement:
--   Under exactly the hypotheses and fixed steps of Theorem 3.14 ($n\ge2$, $0<\bar v_i\le\hat v_i$, $\rho_i>0$, certificate (60) for $m$, steps (63)), an SPTE $\alpha^*$ exists and, for every initialization $\alpha^{(0)}\in[0,1]^n$ and every $k\ge0$,
--   $$
--   \|\alpha^{(T_0+k)}-\alpha^*\|_\infty\le P_{\mathrm{err}}\theta^k,\qquad \|\mathcal R(\alpha^{(T_0+k)})\|_\infty\le Q_{\mathrm{res}}\theta^k,
--   $$
--   with $\theta=1-a\tau_{\min}/2$, $P_{\mathrm{err}}=C_{\mathrm{tri}}W^{n-1}$, $Q_{\mathrm{res}}=(1+L_r)P_{\mathrm{err}}$.
--
--   The result is an R-linear envelope for the single trajectory of (51), including strictly slack and weakly binding caps.
--
--   **Formalization Note** The bounds are stated for every SPTE $\alpha^*$ together with the existence of one; by Theorem 3.14 the SPTE is unique.
--
--   Differences from the source:
--   - generalization: the smallest index wins a tie (§3.2, p.26) → every deterministic single-winner tie rule (AutobidSPPE.TieRule); reason: under independent uniform values ties between values have probability zero, so spending, loss, response and equilibria do not depend on the rule; the smallest-index rule is one instance
--   - encoding: steps (63) for any fixed bidder ordering → StepCondT: there is a permutation σ of Fin n with the inequalities along σ; reason: a fixed ordering of the bidders is a permutation
--   - encoding: J_s = D_α s, the auction spending Jacobian → partial derivatives of the polynomial (57) (spendPoly); reason: the paper's own formula (57), which it states equals the auction spending on [0,1]^n
--   - reading: α* (the unique SPTE) → an SPTE exists, and the bounds hold for every SPTE α*; reason: uniqueness is Theorem 3.14; this form does not presuppose it
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.16, p.37

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_IsBayesianSPTE
import Definitions.Def_AutobidSPPE_Supplement_residualT
import Definitions.Def_AutobidSPPE_Supplement_iterateT
import Definitions.Def_AutobidSPPE_Supplement_PrincipalMinorCert
import Definitions.Def_AutobidSPPE_Supplement_StepCondT
import Definitions.Def_AutobidSPPE_Supplement_PerrT
import Definitions.Def_AutobidSPPE_Supplement_QresT
import Definitions.Def_AutobidSPPE_Supplement_thetaT
import Definitions.Def_AutobidSPPE_T0

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- Theorem 3.16, p.37 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), second stage: geometric last-iterate convergence. Under exactly the hypotheses
and fixed steps of Theorem 3.14 (`n ≥ 2`, `0 < v̄ᵢ ≤ v̂ᵢ`, `ρᵢ > 0`, certificate (60) for `m`, steps (63)), an SPTE
`α*` exists and, for every initialization `α⁽⁰⁾ ∈ [0,1]ⁿ` and every `k ≥ 0`,
`‖α⁽ᵀ⁰⁺ᵏ⁾ − α*‖_∞ ≤ P_err θᵏ` and `‖R(α⁽ᵀ⁰⁺ᵏ⁾)‖_∞ ≤ Q_res θᵏ` (83), with `θ = 1 − aτ_min/2` (79) and `P_err`,
`Q_res` from (80).

**Formalization Note** The bound is stated for every SPTE `α*` (the SPTE is unique by Theorem 3.14), together
with the existence of one. `‖·‖` is the sup norm. Every tie rule is allowed. -/
theorem theorem_3_16 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ)
    (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i) (hρ : ∀ i, 0 < ρ i) (tie : TieRule n)
    (m : ℝ) (hm : PrincipalMinorCert vbar vhat ρ m) (τ : Fin n → ℝ) (hτ : StepCondT vhat ρ m τ) :
    (∃ αstar : Fin n → ℝ, IsBayesianSPTE vbar ρ tie αstar) ∧
    ∀ αstar : Fin n → ℝ, IsBayesianSPTE vbar ρ tie αstar →
      ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) → ∀ k : ℕ,
        ‖iterateT vbar ρ tie τ α0 (T0 τ + k) - αstar‖ ≤ PerrT vhat ρ m * thetaT vhat m τ ^ k ∧
        ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 (T0 τ + k))‖ ≤
          QresT vhat ρ m * thetaT vhat m τ ^ k := by sorry

end AutobidSPPE.Supplement
