-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_3
-- name    : ChurnServiceMode.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:43.995206+00:00
-- url     : https://prove2.me/theorems/bef64e31-b264-41bd-b1aa-4b965dcd201d
-- title:
--   Lemma 3 — uniqueness of the risk-seeking threshold $\theta_G$ (corrected: sign of the erf difference in (11))
-- statement:
--   Let $\mu_R,\mu_S,\sigma_R>0$ with $\mu_R<\mu_S<q$. Let $\Theta^{\rm big}_G$ be the set of roots of display (12) and $\Theta^{\rm small}_G$ the set of roots of the corrected display (11),
--   $$e^{\hat q^2}\frac{\sqrt\pi(\theta-\mu_R)(q-\mu_R)}{\sigma_R^2}\bigl(\operatorname{erf}(\hat\theta)-\operatorname{erf}(\hat q)\bigr)+e^{\hat q^2-\hat\theta^2}\hat q-\hat\theta-\frac{\mu_S\sigma_R}{2(\mu_S-\mu_R)(q-\mu_S)}=0,$$
--   where $\hat q=(q-\mu_R)/\sigma_R$, $\hat\theta=(\theta-\mu_R)/\sigma_R$. Then the set
--   $$\Bigl(\Theta^{\rm big}_G\cap\bigl(\mu_S-\tfrac{\sigma_R^2}{\mu_S-\mu_R},\,\mu_S\bigr)\Bigr)\cup\bigl(\Theta^{\rm small}_G\cap[\mu_S,q)\bigr)$$
--   contains exactly one element, called $\theta_G$. (For $\mu_R\ge\mu_S$ the paper sets $\theta_G=-\infty$.)
--
--   $\theta_G$ is the lower end of the risk-seeking region $(\theta_G,q)$ of the optimal policy.
--
--   Differences from the source:
--   - correction: display (11) of Lemma 3 contains (erf((q−µR)/σR) − erf((θ−µR)/σR)) → smallFn uses (erf((θ−µR)/σR) − erf((q−µR)/σR)); reason: the printed Lemma 3 is false: at (µS, µR, σR, q) = (5, 1, 3, 6) the printed union is {5.59957, 4.48080}, two elements; at (2, 1, 1, 3) the printed θG = 2.94588 gives a policy with V(3) = 2.0945 < 2.2964 for θ = 2.59275, the root of the corrected equation; the proof of Lemma 3 (p.24) defines F_small with (erf θ̂ − erf q̂) and says it is twice the LHS of (11)
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
--   - reading: Assumption 1 (q > µS), imposed "throughout this paper" (p.8) and not repeated in the statement → hypothesis μS < q; reason: standing assumption of the paper; the constant term of (11)–(12) divides by q − µS
--   - encoding: "If µR ≥ µS, let θG = −∞" → part of the definition IsThetaG, not of this statement; reason: it defines θG and claims nothing
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 3 with displays (11)–(12), pp.9–10 (PDF pp.9–10); F_small in the proof, p.24

import Mathlib
import Definitions.Def_ChurnServiceMode_optPolicy

namespace ChurnServiceMode

/-- **Lemma 3** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), pp.9–10; corrected: sign of the erf difference in display (11)). If
`μR < μS` (and `μS < q`, Assumption 1), the set
`(Θ^big_G ∩ (μS − σR²/(μS − μR), μS)) ∪ (Θ^small_G ∩ [μS, q))` contains exactly one element
(labelled `θG`), where `Θ^big_G` is the root set of (12) (`bigFn`) and `Θ^small_G` the root set of
the corrected (11) (`smallFn`). -/
theorem lemma_3 (p : Params) (h : p.μR < p.μS) (hq : p.μS < p.q) :
    ∃! θ : ℝ,
      (θ ∈ Set.Ioo (p.μS - p.σR ^ 2 / (p.μS - p.μR)) p.μS ∧ bigFn p θ = 0) ∨
        (θ ∈ Set.Ico p.μS p.q ∧ smallFn p θ = 0) := by sorry

end ChurnServiceMode
