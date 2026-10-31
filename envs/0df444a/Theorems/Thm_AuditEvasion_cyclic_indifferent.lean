-- Prove2me | Theorems.Thm_AuditEvasion_cyclic_indifferent
-- name    : AuditEvasion.cyclic_indifferent
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:27.770111+00:00
-- url     : https://prove2.me/theorems/4829fa5c-f905-4a74-8e85-e3d29d09c0ad
-- title:
--   §5, p.1851 — under the cyclic policy the agent is indifferent and the policy is feasible (corrected: $h<F$)
-- statement:
--   Assume perfect evasion, $\beta=0$, and $\lambda,\theta,h>0$, $h<F$, $h\le r$. Let $t_0\ge0$ and consider the cyclic policy: after each audit, a deterministic period of length $t_0$ with no audits and payment $P_t=he^{-\theta(\tau_{i-1}+t_0-t)}$, then intensive audits at rate $q^{n\star}=\theta h/(F-h)$ with payment $P_t=h$ until the next audit. Then
--
--   1. the policy is feasible for problem (11): well formed, $P_t\le F$, obedience (6) and the IC constraint hold;
--   2. the agent is indifferent between disclosing at once and any other strategy:
--   $$C_a(P,\sigma)=C_a(P,T)\quad\text{for every strategy }\sigma,$$
--   including never acting.
--
--   Indifference is what the payment ramp (13) and the audit rate (14) are designed for: the discounting gain of a delay is exactly offset by the rise of the payment or by the expected fine.
--
--   Differences from the source:
--   - generalization: the cyclic policy with ramp length t⋆ → every ramp length t₀ ≥ 0; reason: the indifference argument of the passage does not use (12); t₀ = t⋆ is the paper's case
--   - correction: h ≤ F (p.1847, (2)); Theorem 2 prints q^{n⋆} = θh/(F − h) → h < F; reason: at h = F the rate of (14) has a zero denominator and no policy audits 'at a finite constant rate'; the instance β = 0, F = h = 1, r = 2, λ = θ = k = 1 meets every assumption of the paper
--   - reading: 'the agent is indifferent between disclosing the issue immediately … and delaying the disclosure' and the audit rate 'exactly offset[s]' the benefit of delay (Δt heuristics) → the policy is feasible for (11) and C_a(P,σ) = C_a(P,T) for every strategy σ, including never acting; reason: indifference for every infinitesimal delay is equality of the agent's cost for every delay; the passages also assert obedience and the IC
--   - reading: the principal's problem, reformulated as (11) 'subject to (6)–(10)' → minimize (11)'s objective over Feasible policies: §3.1 regularity, P_t ≤ F, obedience (6) and the IC C_a(P,T) ≤ C_a(P,σ) for every strategy σ, with F_t ≡ F; reason: §4 (p.1849) takes F_t = F and states Theorem 2's setting as (11); Theorem 1 part 3 gives the global IC as equivalent to (9)–(10)
--   - reading: (6) 'for all t ≥ 0' → (6) and P_t ≤ F on every public history and every t after its last audit (t ≥ 0 for the empty history); reason: payments at histories that occur with probability 0 never enter a cost, so imposing (6) there changes no optimal value
--   - generalization: damage rate c with r < c/θ (p.1847) → c and r < c/θ omitted; reason: neither enters problem (11) (p.1850: '(11) does not depend on … c'); the statement holds for every r ≥ h and so specializes to the paper's
--   - encoding: agent strategies: stopping times σ(T) ≥ T (§3.5, p.1848) → an action time ≥ T fixed at T as a measurable function of T and the audits before T (⊤ = never act); reason: no audit happens in (T, τ(T)) and an agent who has not acted by τ(T) is caught there, so every non-anticipating stopping time agrees with such a delay where its cost is decided; randomized strategies are averages
--   - encoding: the audit law of a history-dependent schedule (q^m_t, q^n_t) (§3.1; rigorous form in Online Appendix A) → next audit drawn by inverting the conditional survival function exp(−∫q^n)·∏(1 − q^m) with i.i.d. uniform noise; the rate integrable just after each audit (the cumulative intensity may diverge later) and the policy jointly Borel measurable; reason: this realizes the paper's next-audit probabilities exactly; measurability makes the expectations well defined
--   - encoding: expected discounted costs (3) and (11) → EReal: the auditing expense as an ℝ≥0∞ lintegral, the payment term through positive and negative parts; reason: a cost can be +∞ or −∞; no Bochner junk value 0; same value for every policy of finite cost
--   - encoding: τ(T) > T, 'the first audit after the issue has occurred' (§3.5, p.1848) → the first audit at or after T; audits τ_i ≤ T count in the expense and audits < T form H_T; reason: T has a density and is independent of the audits, so T equals an audit epoch with probability 0
--   - encoding: audit schedule Q_t for t ∈ [0,∞) (§3.1, p.1847) → audits at epochs > 0 only, with τ₀ = 0; reason: T > 0 almost surely, so an audit at time 0 detects nothing and only adds its cost k
--   - encoding: threat utility U_t (§3.4; formal definition (A.4) of Online Appendix A, not held) → E[F e^{−θ(D−t)}], with D the first audit at or after t that detects, each audit detecting independently with probability β; reason: this is §3.4's sentence with the recursion (7)–(8); at β = 0 it gives U ≡ 0, as p.1848 states
--   - encoding: (13) on (τ_{i−1}, τ_{i−1} + t⋆] → the same formula also at t = 0 on the empty history; reason: the printed intervals leave P_0 open; T > 0 almost surely, so this value is never charged
-- source:
--   Wang, de Véricourt, Sun, Audit and Remediation Strategies in the Presence of Evasion Capabilities, Oper. Res. 72(5) (2024), doi:10.1287/opre.2022.0289, §5, p.1851 (PDF 10), the two paragraphs after Figure 2

import Mathlib
import Definitions.Def_AuditEvasion_Model
import Definitions.Def_AuditEvasion_AuditProcess
import Definitions.Def_AuditEvasion_Costs
import Definitions.Def_AuditEvasion_CyclicPolicy

namespace AuditEvasion

/-- §5, p.1851 (the two paragraphs after Figure 2), Oper. Res. 72(5) (2024): under perfect
evasion (`β = 0`), for every ramp length `t₀ ≥ 0` the cyclic policy (13)–(14) is feasible for
problem (11), and the agent is indifferent between disclosing at once and every other strategy
(any delay, including never acting): `C_a(P, σ) = C_a(P, T)` for all `σ`.

**Formalization Note** Stated for every `t₀ ≥ 0`, not only `t⋆`: the indifference does not use
(12). -/
theorem cyclic_indifferent (p : Params) (hlam : 0 < p.lam) (htheta : 0 < p.theta)
    (hh : 0 < p.h) (hhF : p.h < p.F) (hhr : p.h ≤ p.r) (hbeta : p.beta = 0)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Feasible p (cyclic p t₀) ∧
      ∀ s : Strategy, agentCost p (cyclic p t₀) s = agentCost p (cyclic p t₀) prompt := by sorry

end AuditEvasion
