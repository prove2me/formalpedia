-- Prove2me | Theorems.Thm_AcquihiringAudit_Bargaining_proposition_2_full_domain
-- name    : AcquihiringAudit.Bargaining.proposition_2_full_domain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:31:35.613966+00:00
-- url     : https://prove2.me/theorems/2396363f-f8fa-4223-b0f1-252f22f02722
-- title:
--   Proposition 2 (corrected: endpoint threshold and failed-bid indifference)
-- statement:
--   Consider a startup, its essential employee and an acquirer. The employee produces real values $v_s$ and $v_a$ at the two firms, respectively, enjoys a private benefit $b$ only at the startup, and must receive at least the real wage floor $\underline w$. Assume $b>0$ and $\min\{v_a,v_s\}>b+\underline w$. Let the acquirer's bargaining power $\alpha$ and the probability $\delta$ of direct hiring after failed bargaining satisfy
--
--   $$0\le\alpha\le1,\qquad 0\le\delta\le1,\qquad 0<\alpha\delta<1.$$
--
--   In direct hiring, both firms offer wages and the employee chooses the larger utility; either choice is allowed at a tie. A continuation equilibrium requires feasible offers capped by each firm's productive value, sequential rationality of the employee at every pair of offers, and no profitable feasible wage deviation. Such an equilibrium exists for every parameter instance here, including $v_a=v_s+b$.
--
--   Let $\sigma_D$ and $\sigma_F$ be any two such equilibria, for initial direct hiring and direct hiring after failed bargaining. They need not coincide. Write $\pi_a^F,\pi_s^F,u_e^F$ for the three continuation payoffs at $\sigma_F$. Set
--
--   $$t_a=\delta\pi_a^F,\quad t_s=\delta\pi_s^F+(1-\delta)(v_s-\underline w),\quad S=v_a-\underline w-t_a-t_s.$$
--
--   Write $C$ for $S>0$, the event that the acquisition occurs, and let $p=t_s+(1-\alpha)S$. Let $D,E_D$ denote the acquirer's and employee's payoffs at $\sigma_D$. Their payoffs from initiating acquihiring are
--
--   $$A=\begin{cases}v_a-\underline w-p&C,\\t_a&\neg C,\end{cases}\qquad E_A=\begin{cases}\underline w&C,\\\delta u_e^F+(1-\delta)(\underline w+b)&\neg C.\end{cases}$$
--
--   Define the lower and upper hiring thresholds by
--
--   $$L=\frac{v_s+\delta(\underline w+b)}{1+\delta},\qquad U=\begin{cases}v_s+b+\dfrac{\alpha[\delta(v_s-\underline w)+b]}{(1-\alpha)(1-\delta)}&\alpha<1,\ \delta<1,\\+\infty&\alpha=1\text{ or }\delta=1.\end{cases}$$
--
--   For every pair of equilibrium continuations, the following conclusions hold:
--
--   1. $L<v_s$ and $v_s+b<U$.
--   2. If $U<v_a$, then $D>A$; direct hiring transfers the employee to the acquirer at wage $v_s+b$.
--   3. If $L<v_a<U$, then $A>D$, the acquisition occurs, and the acquirer employs the worker at wage $\underline w$.
--   4. If $v_a<L$, then no acquisition occurs, and the worker stays at the startup in both direct-hiring continuations. When no wage contest follows failure, she also stays there, at the wage floor.
--   5. The employee comparison is
--
--   $$E_A\le E_D,\qquad (E_A<E_D)\ \Longleftrightarrow\ (C\ \text{or}\ \delta<1).$$
--
--   Thus equality occurs exactly when $\delta=1$ and the acquisition fails. Successful acquisition always strictly harms the employee relative to direct hiring. The strict hiring regions impose no mode selection at $v_a=L$ or finite $v_a=U$; the employee comparison still applies there. Negative wage floors and the tie $v_a=v_s+b$ remain included.
--
--   This is the full-domain corrected Proposition 2, extending the published interior-parameter result while retaining both source milestones. It characterizes the initial hiring decision and its employee-welfare comparison from primitive continuation payoffs.
--
--   Differences from the source:
--   - correction: the real quotient for the upper threshold on the entire allowed parameter domain → the same finite threshold on the interior and +∞ when α = 1 or δ = 1; reason: at (v_a,v_s,b,w̲,α,δ) = (4,5,1,0,1,1/2), all assumptions hold but the denominator is zero and the added numerator is 7/2; the one-sided limits in Corollaries 1–2 support this endpoint value
--   - correction: unconditional strict employee preference, including a failed initial acquisition attempt → weak preference always, strict exactly when the acquisition occurs or δ < 1; reason: at (2,5,1,0,1/2,1), equilibrium offers (w_a,w_s) = (2,1) with ties favoring the startup give employee payoff 2, threat points (0,4), surplus −2, and no acquisition; failure leads to direct hiring with probability 1 and the same employee payoff 2
--   - reading: the employee always prefers direct hiring over acquihiring → compare expected employee payoffs of both initial modes, including the failure lottery; reason: this selects the strongest initial-mode reading; conditioning only on successful acquisition would omit failed attempts
--   - encoding: a finite threshold formula with divergent allowed endpoints → EReal threshold with real arithmetic inside the finite branch and explicit coercions for comparisons; reason: +∞ represents the corrected endpoint; no extended-real subtraction, default division by zero, or excluded real instance is used
--   - encoding: continuation equilibria implicitly exist, including at v_a = v_s + b → an existential equilibrium conjunct before the universal claims over two independent equilibrium profiles; reason: this makes nonvacuity explicit without requiring an equilibrium as an input or removing the wage-value tie
-- source:
--   Bar-Isaac, Johnson and Nocke, Acquihiring for Monopsony Power, CRC TR 224 Discussion Paper No. 500, January 22, 2024, Proposition 2, printed p. 9 / PDF p. 10; https://www.crctr224.de/research/discussion-papers/archive/dp500; PDF SHA-256 1d145f10d566016d690609bf85c10e38505da5adf94960de74e182b3ad469cd9. Standing assumptions: §2, printed pp. 4–5 / PDF pp. 5–6, footnote 13; bargaining protocol: §4, printed pp. 7–8 / PDF pp. 8–9.

import Mathlib
import Definitions.Def_AcquihiringAudit_Bargaining_vUpperExtended
open AcquihiringMonopsony.Baseline
open AcquihiringMonopsony.Bargaining

namespace AcquihiringAudit.Bargaining

/-- Proposition 2, printed p. 9 / PDF 10 (corrected: endpoint threshold and failed-bid
indifference). All standing real parameters and the complete `0 < αδ < 1` domain
are retained. The upper threshold is infinite at either allowed endpoint. Employee
payoffs compare the two initial modes, including bargaining failure; strictness
fails exactly when `δ = 1` and no acquisition occurs. The existence conjunct is
independent of the subsequent universal equilibrium implications and includes
`v_a = v_s + b`. The two continuation equilibria may differ. No mode selection
is imposed at either hiring threshold. The proof-only sign typo in Lemma 3 is
avoided by using its primitive price and payoffs. -/
theorem proposition_2_full_domain (P : Params) (hP : P.Standing) (α δ : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hprod0 : 0 < α * δ) (hprod1 : α * δ < 1) :
    (∃ σ : DHProfile, IsDHEquilibrium P σ) ∧
    (vLower P δ < P.vs ∧ (P.vs + P.b : EReal) < vUpperExtended P α δ) ∧
    (∀ σD σF : DHProfile, IsDHEquilibrium P σD → IsDHEquilibrium P σF →
      (vUpperExtended P α δ < (P.va : EReal) →
        ahPayoffA P α δ σF < dhPayoffA P σD.acceptA σD.wa σD.ws ∧
        σD.acceptA σD.wa σD.ws = true ∧ σD.wa = P.vs + P.b) ∧
      (vLower P δ < P.va → (P.va : EReal) < vUpperExtended P α δ →
        dhPayoffA P σD.acceptA σD.wa σD.ws < ahPayoffA P α δ σF ∧
        AcquisitionOccurs P δ σF ∧ ahPayoffE P δ σF = P.wl) ∧
      (P.va < vLower P δ →
        ¬ AcquisitionOccurs P δ σF ∧
        σD.acceptA σD.wa σD.ws = false ∧ σF.acceptA σF.wa σF.ws = false) ∧
      ahPayoffE P δ σF ≤ dhPayoffE P σD.acceptA σD.wa σD.ws ∧
      (ahPayoffE P δ σF < dhPayoffE P σD.acceptA σD.wa σD.ws ↔
        AcquisitionOccurs P δ σF ∨ δ < 1)) := by sorry

end AcquihiringAudit.Bargaining
