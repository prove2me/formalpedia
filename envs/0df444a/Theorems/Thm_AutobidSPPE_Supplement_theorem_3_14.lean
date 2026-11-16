-- Prove2me | Theorems.Thm_AutobidSPPE_Supplement_theorem_3_14
-- name    : AutobidSPPE.Supplement.theorem_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:03:16.251208+00:00
-- url     : https://prove2.me/theorems/06674fc3-4e0d-425f-ac3a-b23bba3860e4
-- title:
--   Theorem 3.14 — first stage: squared best-iterate residual (throttling)
-- statement:
--   Let $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i$, and budgets $\rho_i>0$ (A1–A3). Suppose $m$ satisfies the principal-minor certificate (60) and the steps satisfy (63) with the constants (62) of that $m$. Then every initialization $\alpha^{(0)}\in[0,1]^n$ of the throttling iteration (51) satisfies
--   $$
--   \sum_{t=0}^{\infty}\|\mathcal R(\alpha^{(t)})\|_\infty^2\le C_{\mathrm{res}}:=T_0+\frac{Q_{\mathrm{res}}^2}{1-\theta^2},\qquad \min_{0\le t<N}\|\mathcal R(\alpha^{(t)})\|_\infty^2\le\frac{C_{\mathrm{res}}}{N},
--   $$
--   and the trajectory converges to the unique SPTE. Here $T_0=\lceil\log2/\tau_{\min}\rceil$, $\theta=1-a\tau_{\min}/2$ and $Q_{\mathrm{res}}=(1+L_r)C_{\mathrm{tri}}W^{n-1}$. In particular, for three bidders with arbitrary supports, Lemma 3.4 supplies the certificate: $m$ of (61) satisfies (60).
--
--   This is the best-iterate guarantee of the source-aligned hierarchy argument for throttling.
--
--   **Formalization Note** The spending Jacobian in (60) is computed from the paper's polynomial (57).
--
--   Differences from the source:
--   - generalization: the smallest index wins a tie (§3.2, p.26) → every deterministic single-winner tie rule (AutobidSPPE.TieRule); reason: under independent uniform values ties between values have probability zero, so spending, loss, response and equilibria do not depend on the rule; the smallest-index rule is one instance
--   - encoding: an infinite sum of squared residuals → a bound on every partial sum; reason: the terms are nonnegative, so the two are equivalent
--   - encoding: min over 0 ≤ t < N → some t < N; reason: the minimum of finitely many reals is attained
--   - encoding: steps (63) for any fixed bidder ordering → StepCondT: there is a permutation σ of Fin n with the inequalities along σ; reason: a fixed ordering of the bidders is a permutation
--   - encoding: J_s = D_α s, the auction spending Jacobian → partial derivatives of the polynomial (57) (spendPoly); reason: the paper's own formula (57), which it states equals the auction spending on [0,1]^n
--   - reading: In particular, for three arbitrarily heterogeneous uniforms, Lemma 3.4 supplies the certificate (61) → n = 3 → PrincipalMinorCert v̄ v̂ ρ (mThree v̄ v̂ ρ); reason: the sentence asserts that m of (61) is a certificate; with the first part this gives the conclusions for n = 3
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.14, p.37

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_IsBayesianSPTE
import Definitions.Def_AutobidSPPE_Supplement_residualT
import Definitions.Def_AutobidSPPE_Supplement_iterateT
import Definitions.Def_AutobidSPPE_Supplement_PrincipalMinorCert
import Definitions.Def_AutobidSPPE_Supplement_StepCondT
import Definitions.Def_AutobidSPPE_Supplement_mThree
import Definitions.Def_AutobidSPPE_Supplement_CresT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- Theorem 3.14, p.37 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), first stage: squared best-iterate residual. Let `n ≥ 2`, `vᵢ ∼ Unif[0, v̄ᵢ]`
independently with `0 < v̄ᵢ ≤ v̂ᵢ`, and `ρᵢ > 0` (A1–A3). If `m` satisfies the certificate (60) and the steps
satisfy (63) with the constants (62) of that `m`, then every initialization `α⁽⁰⁾ ∈ [0,1]ⁿ` satisfies
`Σ_{t≥0} ‖R(α⁽ᵗ⁾)‖²_∞ ≤ C_res = T₀ + Q_res²/(1 − θ²)` and `min_{0≤t<N} ‖R(α⁽ᵗ⁾)‖²_∞ ≤ C_res/N` (82), and the
trajectory converges to the unique SPTE. In particular, for three bidders with arbitrary supports, Lemma 3.4
supplies the certificate (61): `m` of (61) satisfies (60).

**Formalization Note** The infinite sum of nonnegative terms is stated as a bound on every partial sum.
"min over `0 ≤ t < N`" is "some `t < N`". `‖·‖` is the sup norm. Every tie rule is allowed. -/
theorem theorem_3_14 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ)
    (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i) (hρ : ∀ i, 0 < ρ i) (tie : TieRule n) :
    (∀ m : ℝ, PrincipalMinorCert vbar vhat ρ m → ∀ τ : Fin n → ℝ, StepCondT vhat ρ m τ →
      ∃ αstar : Fin n → ℝ, IsBayesianSPTE vbar ρ tie αstar ∧
        (∀ β, IsBayesianSPTE vbar ρ tie β → β = αstar) ∧
        ∀ α0 : Fin n → ℝ, (∀ i, α0 i ∈ Set.Icc (0 : ℝ) 1) →
          (∀ N : ℕ, ∑ t ∈ Finset.range N,
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤ CresT vhat ρ m τ) ∧
          (∀ N : ℕ, 1 ≤ N → ∃ t < N,
            ‖residualT vbar ρ tie (iterateT vbar ρ tie τ α0 t)‖ ^ 2 ≤ CresT vhat ρ m τ / N) ∧
          Filter.Tendsto (iterateT vbar ρ tie τ α0) Filter.atTop (nhds αstar)) ∧
    (n = 3 → PrincipalMinorCert vbar vhat ρ (mThree vbar vhat ρ)) := by sorry

end AutobidSPPE.Supplement
