-- Prove2me | Theorems.Thm_FinDisclosure_Threshold_proposition_1
-- name    : FinDisclosure.Threshold.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:20:29.871686+00:00
-- url     : https://prove2.me/theorems/c9b21a8b-01a3-4bc3-a6d9-80d0f236cbb8
-- title:
--   Proposition 1, p. 18 — if E_µ0 c < I (and λI ≤ B), revealing whether s ≥ ŝ, with ŝ making the financing constraint bind, is an optimal Bayes-plausible policy
-- statement:
--   An entrepreneur must raise an investment cost $I$ by selling a security $c(s)$ on a project with payoff $s \in [0,1]$ to competitive investors, and commits beforehand to a disclosure policy. Assume the standing assumptions of the model (§2), §4's assumption $\mathbb E_{\mu_0} c(s) < I$ (the project cannot be financed without disclosure), and $\lambda I \le B$.
--
--   Then there is a threshold $\hat s \in (0,1]$ at which the financing constraint (20) binds,
--   $$\int_{\hat s}^1 \big(c(s) - I\big)\,\mu_0(s)\,ds = 0,$$
--   such that the policy that truthfully reveals whether $s \ge \hat s$ or $s < \hat s$ is Bayes plausible and optimal: for every Bayes-plausible distribution $\tau$ over posteriors,
--   $$\mathbb E_\tau V(\mu) \;\le\; \mathbb E_{\tau_{\hat s}} V(\mu),$$
--   where $V$ is the entrepreneur's payoff (3) and $\tau_{\hat s}$ is the threshold policy.
--
--   This is the paper's main result. The optimal disclosure is a pass/fail test whose standard is set exactly where the investors break even.
--
--   **Formalization Note** The comparison class is every Bayes-plausible distribution over posteriors, problem (6), not only threshold or two-point policies. The policy is *an* optimal policy: uniqueness fails, since splitting the unfinanced cell does not change the value. $\hat s = 1$ is allowed: if $c(1) < I$ nothing can ever be financed, and revealing nothing is optimal with value $0$. The hypothesis $\lambda I \le B$ is not in the paper, and the proposition is false without it. With $\mu_0 = 1$ on $[0,1]$, $c(s) = s$, $I = 0.6$, $B = 0.1$ and $\lambda = 1$, the binding threshold $\hat s = 0.2$ earns $0.08$, while revealing whether $s \ge 0.5$ earns $0.5\,(0.1 + 1\cdot(0.75 - 0.6)) = 0.125$. It covers $\lambda = 0$, the case of §5. Ties in the financing rule go to financing ($p(\mu) \ge I$), as in (2).
-- source:
--   Szydlowski, Optimal Financing and Disclosure, working paper (version of March 2017), p. 18 (PDF 18), Proposition 1, eq. (20); proof pp. 33–39 (PDF 33–39), §A.2

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace FinDisclosure.Threshold

/-- Proposition 1, p. 18 (under §4's standing assumption `E_{µ0} c(s) < I`, p. 15, and the added
hypothesis `λ I ≤ B`): there is a threshold `ŝ ∈ (0, 1]` at which the financing constraint (20)
binds, `∫_ŝ^1 (c(s) - I) µ0(s) ds = 0`, such that truthfully revealing whether `s ≥ ŝ` or `s < ŝ` is
a Bayes-plausible distribution over posteriors whose value is at least that of every Bayes-plausible
distribution over posteriors. -/
theorem proposition_1 (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hEc : ∫ s in (0:ℝ)..1, c s * f0 s < I) (hB : lam * I ≤ B) :
    ∃ shat : ℝ, 0 < shat ∧ shat ≤ 1 ∧ ∫ s in shat..1, (c s - I) * f0 s = 0 ∧
      IsBayesPlausible (prior f0) (thresholdPolicy f0 shat) ∧
      ∀ τ : Measure (Measure ℝ), IsBayesPlausible (prior f0) τ →
        value c I B lam τ ≤ value c I B lam (thresholdPolicy f0 shat) := by sorry

end FinDisclosure.Threshold
