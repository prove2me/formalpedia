-- Prove2me | Theorems.Thm_AuditEvasion_theorem_2
-- name    : AuditEvasion.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:38.027027+00:00
-- url     : https://prove2.me/theorems/19f328ab-5f6e-4f42-913d-83c806f3b248
-- title:
--   Theorem 2, p.1850 — under perfect evasion a cyclic policy with exponential random audits is optimal (corrected: $h<F$)
-- statement:
--   Assume perfect evasion, $\beta=0$, with $\lambda,\theta,k,h>0$, $h<F$ and $h\le r$. Then:
--
--   1. the equation $\Gamma(t;h)=(\lambda+\theta)[F-(k+F)e^{-\lambda t}]-\lambda h[1-e^{-(\lambda+\theta)t}]=0$ (12) has a unique positive solution $t^\star$;
--
--   and for this $t^\star$, the cyclic policy $(P^\star,Q^\star)$, which after each audit $\tau_{i-1}$ ($\tau_0=0$) runs no audits and charges
--   $$P^\star_t=he^{-\theta(\tau_{i-1}+t^\star-t)},\qquad t\in(\tau_{i-1},\tau_{i-1}+t^\star],\qquad(13)$$
--   and then runs only intensive audits at the constant rate with a constant payment
--   $$q^{n\star}=\frac{\theta h}{F-h},\qquad P^\star_t\equiv h,\qquad t\in(\tau_{i-1}+t^\star,\tau_i],\qquad(14)$$
--   satisfies
--
--   2. $(P^\star,Q^\star)$ is feasible for problem (11) (obedience (6) and the IC constraint);
--   3. its cost (11) is no larger than that of **every** feasible policy, i.e. every history-dependent schedule of impulsive and intensive audits with every payment process satisfying (6) and the IC;
--   4. under it every audit epoch $\tau_i$ is finite almost surely, and the times $\tau_i-\tau_{i-1}-t^\star$, $i=1,2,\dots$, are independent and exponentially distributed with rate $q^{n\star}$.
--
--   The theorem shows that the agent's ability to evade forces the principal to audit at random: each cycle opens with a deterministic, increasing disclosure payment and closes with an exponentially distributed wait for an audit.
--
--   **Formalization Note** $\beta$ is a parameter of the model and $\beta=0$ is a hypothesis; with $\beta=0$ the threat utility vanishes.
--
--   Differences from the source:
--   - correction: h ≤ F (p.1847, (2)); Theorem 2 prints q^{n⋆} = θh/(F − h) → h < F; reason: at h = F the rate of (14) has a zero denominator and no policy audits 'at a finite constant rate'; the instance β = 0, F = h = 1, r = 2, λ = θ = k = 1 meets every assumption of the paper
--   - reading: t⋆ 'the unique solution' of (12) → the unique positive solution of (12); reason: Γ(0) = −(λ+θ)k < 0 and Γ(t) → +∞ as t → −∞, so (12) also has a negative root; Theorem 3 (p.1852) calls the root of the same equation the 'unique positive solution'
--   - reading: 'the principal's optimal policy (P⋆,Q⋆) exhibits a cyclic structure' → cyclic t⋆ is feasible and its cost is ≤ the cost of every feasible policy; reason: optimal policies are not unique (raising π⋆'s payment to h at a single instant of the first ramp keeps (6), the IC and the cost), so the theorem exhibits an optimal policy
--   - reading: the principal's problem, reformulated as (11) 'subject to (6)–(10)' → minimize (11)'s objective over Feasible policies: §3.1 regularity, P_t ≤ F, obedience (6) and the IC C_a(P,T) ≤ C_a(P,σ) for every strategy σ, with F_t ≡ F; reason: §4 (p.1849) takes F_t = F and states Theorem 2's setting as (11); Theorem 1 part 3 gives the global IC as equivalent to (9)–(10)
--   - reading: (6) 'for all t ≥ 0' → (6) and P_t ≤ F on every public history and every t after its last audit (t ≥ 0 for the empty history); reason: payments at histories that occur with probability 0 never enter a cost, so imposing (6) there changes no optimal value
--   - reading: audit cost k (sign not stated, p.1847) → 0 < k; reason: Corollary 1 asserts A⋆ > 0, which needs k > 0
--   - generalization: damage rate c with r < c/θ (p.1847) → c and r < c/θ omitted; reason: neither enters problem (11) (p.1850: '(11) does not depend on … c'); the statement holds for every r ≥ h and so specializes to the paper's
--   - encoding: agent strategies: stopping times σ(T) ≥ T (§3.5, p.1848) → an action time ≥ T fixed at T as a measurable function of T and the audits before T (⊤ = never act); reason: no audit happens in (T, τ(T)) and an agent who has not acted by τ(T) is caught there, so every non-anticipating stopping time agrees with such a delay where its cost is decided; randomized strategies are averages
--   - encoding: the audit law of a history-dependent schedule (q^m_t, q^n_t) (§3.1; rigorous form in Online Appendix A) → next audit drawn by inverting the conditional survival function exp(−∫q^n)·∏(1 − q^m) with i.i.d. uniform noise; the rate integrable just after each audit (the cumulative intensity may diverge later) and the policy jointly Borel measurable; reason: this realizes the paper's next-audit probabilities exactly; measurability makes the expectations well defined
--   - encoding: expected discounted costs (3) and (11) → EReal: the auditing expense as an ℝ≥0∞ lintegral, the payment term through positive and negative parts; reason: a cost can be +∞ or −∞; no Bochner junk value 0; same value for every policy of finite cost
--   - encoding: 'conditional on τ_{i−1}, … τ_i − τ_{i−1} − t⋆ is an i.i.d. exponential random variable with rate q^{n⋆}'; 'persists' → every audit epoch finite a.s., the gaps τ_i − τ_{i−1} − t⋆ (τ₀ = 0) independent (iIndepFun), each with law expMeasure(θh/(F − h)); reason: an independent sequence with this law is the conditional statement; a.s. finiteness is the persistence of the cycles
--   - encoding: τ(T) > T, 'the first audit after the issue has occurred' (§3.5, p.1848) → the first audit at or after T; audits τ_i ≤ T count in the expense and audits < T form H_T; reason: T has a density and is independent of the audits, so T equals an audit epoch with probability 0
--   - encoding: audit schedule Q_t for t ∈ [0,∞) (§3.1, p.1847) → audits at epochs > 0 only, with τ₀ = 0; reason: T > 0 almost surely, so an audit at time 0 detects nothing and only adds its cost k
--   - encoding: threat utility U_t (§3.4; formal definition (A.4) of Online Appendix A, not held) → E[F e^{−θ(D−t)}], with D the first audit at or after t that detects, each audit detecting independently with probability β; reason: this is §3.4's sentence with the recursion (7)–(8); at β = 0 it gives U ≡ 0, as p.1848 states
--   - encoding: (13) on (τ_{i−1}, τ_{i−1} + t⋆] → the same formula also at t = 0 on the empty history; reason: the printed intervals leave P_0 open; T > 0 almost surely, so this value is never charged
-- source:
--   Wang, de Véricourt, Sun, Audit and Remediation Strategies in the Presence of Evasion Capabilities, Oper. Res. 72(5) (2024), doi:10.1287/opre.2022.0289, Theorem 2, (12)–(14), p.1850 (PDF 9)

import Mathlib
import Definitions.Def_AuditEvasion_Model
import Definitions.Def_AuditEvasion_AuditProcess
import Definitions.Def_AuditEvasion_Costs
import Definitions.Def_AuditEvasion_Gamma
import Definitions.Def_AuditEvasion_CyclicPolicy

open MeasureTheory ProbabilityTheory

namespace AuditEvasion

/-- Theorem 2, Oper. Res. 72(5) (2024), p.1850 (corrected: `h < F`): if `β = 0`, then
(a) equation (12) `Γ(t; h) = 0` has a unique positive solution `t⋆`; and for it
(b) the cyclic policy `cyclic p t⋆` of (13)–(14) is feasible for problem (11);
(c) its cost is the least among all feasible policies of (11);
(d) under it every audit epoch is finite almost surely, and the times
`τ_i − τ_{i−1} − t⋆` (`τ₀ = 0`) are independent, each exponential with rate
`q^{n⋆} = θh/(F − h)`.

**Formalization Note** The printed theorem allows `h = F` (p.1847), where the rate of (14) is
undefined; `h < F` is added. -/
theorem theorem_2 (p : Params) (hlam : 0 < p.lam) (htheta : 0 < p.theta) (hk : 0 < p.k)
    (hh : 0 < p.h) (hhF : p.h < p.F) (hhr : p.h ≤ p.r) (hbeta : p.beta = 0) :
    (∃! t : ℝ, 0 < t ∧ Gamma p t = 0) ∧
      ∀ t : ℝ, 0 < t → Gamma p t = 0 →
        Feasible p (cyclic p t) ∧
        (∀ π : Policy, Feasible p π → principalCost p (cyclic p t) ≤ principalCost p π) ∧
        (∀ᵐ v ∂auditNoise, ∀ i, epoch (cyclic p t) v i ≠ ⊤) ∧
        iIndepFun (fun (i : ℕ) (v : ℕ → unitInterval) =>
            (epoch (cyclic p t) v (i + 1)).toReal - (epoch (cyclic p t) v i).toReal - t)
          auditNoise ∧
        ∀ i : ℕ, Measure.map (fun v : ℕ → unitInterval =>
            (epoch (cyclic p t) v (i + 1)).toReal - (epoch (cyclic p t) v i).toReal - t)
          auditNoise = expMeasure (cyclicRate p) := by sorry

end AuditEvasion
