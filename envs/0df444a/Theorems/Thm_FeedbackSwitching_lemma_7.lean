-- Prove2me | Theorems.Thm_FeedbackSwitching_lemma_7
-- name    : FeedbackSwitching.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:41.97886+00:00
-- url     : https://prove2.me/theorems/6853c3f7-f2a1-4ef8-981c-c39da49cebdd
-- title:
--   Lemma 7 — PrepareBlock turns an assignment into a $128\log(e/v_{\min})$-balanced estimator
-- statement:
--   Let $v,w$ be positive probability vectors with $\tfrac12w\le v\le2w$, let $((Q_s)_s,\rho)\in\mathcal C(v)$ satisfy $\sum_s\rho_s\le3\log(e/v_{\min})$, and let $0<\kappa\le1/32$. Put $q=\rho/\sum_j\rho_j$, $p=(1-4\kappa)w+4\kappa q$, $x=(p+q)/2$ and $\Psi_s=C_wQ_s/p_s$. Then
--
--   1. $(p,x)$ is a holding family (positive probability vectors, $x\ge p/2$) with $\kappa\lambda_{\max}<1/4$;
--   2. $w\le\tfrac87p$ and $\|p-w\|_1\le8\kappa$;
--   3. $(\Psi_s)_s$ is an $L_0$-balanced estimator for $(w,p,x)$ with $L_0=128\log(e/v_{\min})$.
--
--   **Formalization Note** $\mathcal C(v)$ is taken for the selected tournament, which also defines the comparisons of Definition 5(i). $\kappa\lambda_{\max}<1/4$ is written for every $s$.
--
--   Differences from the source:
--   - encoding: κλ_max < 1/4; C(v) of Definition 3 (for the selected tournament of §3.2) → κλ_s < 1/4 for every s; C(v) and the comparisons of Definition 5(i) for a tournament A given as a hypothesis; reason: λ_max is a maximum over finitely many actions; the tournament is the standing selected orientation on which Definition 3 is built; same instances
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Lemma 7, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_FeedbackSwitching_CSet
import Definitions.Def_FeedbackSwitching_IsBalancedEstimator
import Definitions.Def_FeedbackSwitching_prepareBlock

namespace FeedbackSwitching

/-- **Lemma 7 (Balanced estimator from an assignment)**, p.29 (PDF p.31). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"Let `v, w` be positive probability vectors with `w/2 ≤ v ≤ 2w`, let `((Q_s)_s, ρ) ∈ C(v)` satisfy
`∑_s ρ_s ≤ 3 log(e/v_min)`, and let `0 < κ ≤ 1/32`. Put `q = ρ/∑_j ρ_j`, `p = (1 − 4κ)w + 4κq`,
`x = (p + q)/2`, and `Ψ_s = C_w Q_s/p_s`. Then `(p, x)` is a holding family with `κλ_max < 1/4`,
`w ≤ (8/7)p`, and `‖p − w‖_1 ≤ 8κ`. Moreover, `(Ψ_s)_s` is an `L₀`-balanced estimator for
`(w, p, x)` with `L₀ = 128 log(e/v_min)`."

**Formalization Note.** `C(v)` is taken for the selected tournament `A` (its support constraint
uses `N⁺(s)`), which is also the tournament of the comparisons in Definition 5 (i).
`κλ_max < 1/4` is written for every `s`. -/
theorem lemma_7 {K : ℕ} (A : Fin K → Fin K → Prop) (hA : IsTournament A) (v w : Fin K → ℝ)
    (hv : IsPosProbVec v) (hw : IsPosProbVec w) (hvw : ∀ i, w i / 2 ≤ v i ∧ v i ≤ 2 * w i)
    (z : (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ)) (hz : z ∈ CSet A v)
    (hρ : ∑ s, z.2 s ≤ 3 * Real.log (Real.exp 1 / vmin v)) (κ : ℝ) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1 / 32) :
    IsHoldingPair (prepP κ w z.2) (prepX κ w z.2) ∧
    (∀ s, κ * lam (prepP κ w z.2) (prepX κ w z.2) s < 1 / 4) ∧
    (∀ i, w i ≤ 8 / 7 * prepP κ w z.2 i) ∧
    ∑ i, |prepP κ w z.2 i - w i| ≤ 8 * κ ∧
    IsBalancedEstimator A w (prepP κ w z.2) (prepX κ w z.2) (prepareBlock κ w z)
      (128 * Real.log (Real.exp 1 / vmin v)) := by sorry

end FeedbackSwitching
