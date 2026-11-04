-- Prove2me | Theorems.Thm_ChurnServiceMode_theorem_1
-- name    : ChurnServiceMode.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:52.947113+00:00
-- url     : https://prove2.me/theorems/2f18b84b-7634-45aa-be79-73b68eb11ef8
-- title:
--   Theorem 1 — a myopic-or-sandwich interval policy is optimal (corrected: sign of the erf difference in Lemma 3's (11))
-- statement:
--   Fix $\mu_R,\mu_S,\sigma_R>0$ and a satisfaction threshold $q$ with $\mu_S<q$. Let $\theta_b$ be the threshold of Lemma 2 and $\theta_G$ that of Lemma 3. Consider the policy $\bar\pi$ that uses
--   - the Safe mode on $[q,\theta_b]$,
--   - the Risky mode on $(\theta_G,q)$,
--   - the superior of the two modes elsewhere.
--
--   Then:
--   1. the thresholds $\theta_b$ and $\theta_G$ exist;
--   2. from every starting satisfaction $x$ there is a control system that follows $\bar\pi$;
--   3. every control system started at $x$ that follows $\bar\pi$ attains the optimal CLV,
--   $$\mathrm{CLV}=V^*(x)=\sup_{\pi\in\Pi}V(x,\pi),$$
--   and has a finite expected lifetime $\mathbb E[T]<\infty$;
--   4. $V^*(x)<\infty$ for every $x$, so the CLV is finite under every admissible policy.
--
--   So the optimal policy is either myopic (always the superior mode) or a "sandwich" policy that uses the inferior mode in one bounded band next to the threshold, and it is optimal among all admissible policies, not only among interval or Markov ones.
--
--   Differences from the source:
--   - correction: display (11) of Lemma 3 contains (erf((q−µR)/σR) − erf((θ−µR)/σR)) → smallFn uses (erf((θ−µR)/σR) − erf((q−µR)/σR)); reason: the printed Lemma 3 is false: at (µS, µR, σR, q) = (5, 1, 3, 6) the printed union is {5.59957, 4.48080}, two elements; at (2, 1, 1, 3) the printed θG = 2.94588 gives a policy with V(3) = 2.0945 < 2.2964 for θ = 2.59275, the root of the corrected equation; the proof of Lemma 3 (p.24) defines F_small with (erf θ̂ − erf q̂) and says it is twice the LHS of (11)
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
--   - generalization: admissible policies π ∈ Π of Definition 1 (adapted control on the given filtered space, processes specified uniquely in law, integrals of (7) existing) → every ControlSystem: any filtered probability space carrying a standard Brownian motion, a progressively measurable {R,S}-valued control and a continuous adapted solution of (3) (weak formulation; uniqueness in law not required); reason: every admissible policy gives such a system (progressive measurability is what makes the integrals of (1) exist), so the class contains Π and the statement specializes to the paper's
--   - reading: CLV (7): E[∫₀^∞ µ_{u_t} 1{t<T} dt + ∫₀^∞ σ_{u_t} 1{t<T} dB_t] → clv := E[∫₀^∞ µ_{u_t} 1{t<T} dt] in [0, ∞] on P ⊗ U[0,1], T as in (6) with inf ∅ = ∞; reason: footnote 6 (p.7) drops the stochastic integral as having zero expectation; the remaining term is what (9) and the proofs use
--   - reading: "there is an optimal policy" π̄ (with its processes specified uniquely in law) → a π̄-feedback ControlSystem exists from every x and every π̄-feedback ControlSystem attains V*; reason: covers the policy's process also where its law is not unique (Lemma 1 correction C3)
--   - encoding: θb = +∞, θG = −∞; "the superior of the two modes" when µR = µS → EReal ⊤, ⊥; Safe; reason: the "elsewhere" set is empty when µR = µS (footnote 11)
--   - encoding: time t ≥ 0; continuous paths → time in ℝ≥0; every path of H and B continuous; reason: standard convention for continuous diffusions; same instances up to modification
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Theorem 1 and footnote 11, p.10 (PDF p.10); Lemmas 2–3, pp.9–10

import Mathlib
import Definitions.Def_ChurnServiceMode_optPolicy
import Definitions.Def_ChurnServiceMode_ControlSystem

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **Theorem 1** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.10; corrected: sign of the erf difference in Lemma 3's display (11)).
Fix `μR, μS, σR > 0` and a satisfaction threshold `q > μS`. Let `θb` be the threshold of Lemma 2
and `θG` the threshold of Lemma 3. Then the policy `π̄` that is Safe on `[q, θb]`, Risky on
`(θG, q)` and uses the superior mode elsewhere is optimal among all control systems: from every
starting satisfaction `x` a `π̄`-feedback system exists, every `π̄`-feedback system attains the
optimal CLV `V*(x)` and has a finite expected lifetime, and `V*(x)` is finite (so the CLV is finite
under any admissible policy).

**Formalization Note.** Control systems are the weak formulation (`ControlSystem`, reading R2);
the CLV drops the zero-mean stochastic integral of (7) (footnote 6, reading R3); `θb, θG : EReal`;
`θG` uses the corrected (11) (`smallFn`, Correction C1). The first conjunct asserts that the
thresholds exist, so the universally quantified part is not vacuous. -/
theorem theorem_1 (p : Params) (hq : p.μS < p.q) :
    ((∃ θb, IsThetaB p θb) ∧ (∃ θG, IsThetaG p θG)) ∧
    ∀ θb θG : EReal, IsThetaB p θb → IsThetaG p θG →
      (∀ x : ℝ, ∃ S : ControlSystem p x, S.IsFeedback (optPolicy p θb θG)) ∧
      (∀ (x : ℝ) (S : ControlSystem p x), S.IsFeedback (optPolicy p θb θG) →
          S.clv = optimalCLV p x ∧ S.expectedLifetime < ⊤) ∧
      (∀ x : ℝ, optimalCLV p x < ⊤) := by sorry

end ChurnServiceMode
