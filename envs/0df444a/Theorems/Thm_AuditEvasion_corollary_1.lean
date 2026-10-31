-- Prove2me | Theorems.Thm_AuditEvasion_corollary_1
-- name    : AuditEvasion.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:29.283574+00:00
-- url     : https://prove2.me/theorems/0d4c6a8a-094c-4449-b599-f18f5eac76ed
-- title:
--   Corollary 1, p.1851 — the costs $C^\star$, $C^\star_a$, $A^\star$ of the optimal cyclic policy (corrected: $h<F$)
-- statement:
--   Assume $\beta=0$, $\lambda,\theta,k,h>0$, $h<F$, $h\le r$, and let $t^\star>0$ solve (12). Under the cyclic policy with ramp length $t^\star$ (the policy of Theorem 2), let $C^\star$ be the principal's cost (11), $C^\star_a$ the agent's cost under prompt disclosure, and $A^\star=E\big[k\sum_{\tau_i\le T}e^{-\theta\tau_i}\big]$ the principal's total auditing expense. Then
--
--   $$C^\star=\frac{\lambda}{\lambda+\theta}\big(r-he^{-\theta t^\star}\big),\qquad C^\star_a=\frac{\lambda}{\lambda+\theta}he^{-\theta t^\star}+A^\star,\qquad A^\star=\frac{\theta}{\lambda+\theta}\cdot\frac{khe^{-\theta t^\star}}{k+F-he^{-\theta t^\star}},$$
--
--   and $C^\star>0$, $C^\star_a>A^\star>0$.
--
--   In particular the agent's expected payment exceeds the principal's auditing expense: the principal shifts the whole auditing cost onto the agent.
--
--   Differences from the source:
--   - correction: h ≤ F (p.1847, (2)); Theorem 2 prints q^{n⋆} = θh/(F − h) → h < F; reason: at h = F the rate of (14) has a zero denominator and no policy audits 'at a finite constant rate'; the instance β = 0, F = h = 1, r = 2, λ = θ = k = 1 meets every assumption of the paper
--   - reading: 'Under the optimal policy (P⋆,Q⋆) specified in Theorem 2' → for cyclic t with t > 0 and Γ(t) = 0; reason: this is the policy of Theorem 2; its costs do not need its optimality
--   - reading: t⋆ 'the unique solution' of (12) → the unique positive solution of (12); reason: Γ(0) = −(λ+θ)k < 0 and Γ(t) → +∞ as t → −∞, so (12) also has a negative root; Theorem 3 (p.1852) calls the root of the same equation the 'unique positive solution'
--   - reading: C⋆, C⋆_a and 'the principal's total auditing expense' A⋆ → C⋆ = principalCost (11), C⋆_a = agentCost under prompt disclosure, A⋆ = E[k Σ_{τ_i ≤ T} e^{−θτ_i}]; reason: (11) and (3) are the paper's cost definitions; A⋆ is the audit term k∫_0^T e^{−θt}dN_t of (11)
--   - reading: audit cost k (sign not stated, p.1847) → 0 < k; reason: Corollary 1 asserts A⋆ > 0, which needs k > 0
--   - generalization: damage rate c with r < c/θ (p.1847) → c and r < c/θ omitted; reason: neither enters problem (11) (p.1850: '(11) does not depend on … c'); the statement holds for every r ≥ h and so specializes to the paper's
--   - encoding: agent strategies: stopping times σ(T) ≥ T (§3.5, p.1848) → an action time ≥ T fixed at T as a measurable function of T and the audits before T (⊤ = never act); reason: no audit happens in (T, τ(T)) and an agent who has not acted by τ(T) is caught there, so every non-anticipating stopping time agrees with such a delay where its cost is decided; randomized strategies are averages
--   - encoding: the audit law of a history-dependent schedule (q^m_t, q^n_t) (§3.1; rigorous form in Online Appendix A) → next audit drawn by inverting the conditional survival function exp(−∫q^n)·∏(1 − q^m) with i.i.d. uniform noise; the rate integrable just after each audit (the cumulative intensity may diverge later) and the policy jointly Borel measurable; reason: this realizes the paper's next-audit probabilities exactly; measurability makes the expectations well defined
--   - encoding: expected discounted costs (3) and (11) → EReal: the auditing expense as an ℝ≥0∞ lintegral, the payment term through positive and negative parts; reason: a cost can be +∞ or −∞; no Bochner junk value 0; same value for every policy of finite cost
--   - encoding: τ(T) > T, 'the first audit after the issue has occurred' (§3.5, p.1848) → the first audit at or after T; audits τ_i ≤ T count in the expense and audits < T form H_T; reason: T has a density and is independent of the audits, so T equals an audit epoch with probability 0
--   - encoding: audit schedule Q_t for t ∈ [0,∞) (§3.1, p.1847) → audits at epochs > 0 only, with τ₀ = 0; reason: T > 0 almost surely, so an audit at time 0 detects nothing and only adds its cost k
--   - encoding: threat utility U_t (§3.4; formal definition (A.4) of Online Appendix A, not held) → E[F e^{−θ(D−t)}], with D the first audit at or after t that detects, each audit detecting independently with probability β; reason: this is §3.4's sentence with the recursion (7)–(8); at β = 0 it gives U ≡ 0, as p.1848 states
--   - encoding: (13) on (τ_{i−1}, τ_{i−1} + t⋆] → the same formula also at t = 0 on the empty history; reason: the printed intervals leave P_0 open; T > 0 almost surely, so this value is never charged
-- source:
--   Wang, de Véricourt, Sun, Audit and Remediation Strategies in the Presence of Evasion Capabilities, Oper. Res. 72(5) (2024), doi:10.1287/opre.2022.0289, Corollary 1, p.1851 (PDF 10)

import Mathlib
import Definitions.Def_AuditEvasion_Model
import Definitions.Def_AuditEvasion_AuditProcess
import Definitions.Def_AuditEvasion_Costs
import Definitions.Def_AuditEvasion_Gamma
import Definitions.Def_AuditEvasion_CyclicPolicy

namespace AuditEvasion

/-- Corollary 1, Oper. Res. 72(5) (2024), p.1851: under the policy of Theorem 2 (`β = 0`, ramp
length `t⋆` the positive root of (12)), the principal's cost is `C⋆ = λ/(λ+θ)(r − h e^{−θt⋆})`,
the agent's cost is `C⋆_a = λ/(λ+θ) h e^{−θt⋆} + A⋆`, the auditing expense is
`A⋆ = θ/(λ+θ) · k h e^{−θt⋆}/(k + F − h e^{−θt⋆})`, and `C⋆ > 0`, `C⋆_a > A⋆ > 0`. -/
theorem corollary_1 (p : Params) (hlam : 0 < p.lam) (htheta : 0 < p.theta) (hk : 0 < p.k)
    (hh : 0 < p.h) (hhF : p.h < p.F) (hhr : p.h ≤ p.r) (hbeta : p.beta = 0)
    (t : ℝ) (ht : 0 < t) (hΓ : Gamma p t = 0) :
    principalCost p (cyclic p t) =
        ((p.lam / (p.lam + p.theta) * (p.r - p.h * Real.exp (-p.theta * t)) : ℝ) : EReal) ∧
      agentCost p (cyclic p t) prompt =
        ((p.lam / (p.lam + p.theta) * p.h * Real.exp (-p.theta * t) : ℝ) : EReal) +
          (auditExpense p (cyclic p t) : EReal) ∧
      (auditExpense p (cyclic p t) : EReal) =
        ((p.theta / (p.lam + p.theta) *
            (p.k * p.h * Real.exp (-p.theta * t) / (p.k + p.F - p.h * Real.exp (-p.theta * t)))
            : ℝ) : EReal) ∧
      0 < principalCost p (cyclic p t) ∧
      (auditExpense p (cyclic p t) : EReal) < agentCost p (cyclic p t) prompt ∧
      0 < auditExpense p (cyclic p t) := by sorry

end AuditEvasion
