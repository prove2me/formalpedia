-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_proof_thm1_pi0_pi1
-- name    : DigitalPrivacy.DataStrategy.proof_thm1_pi0_pi1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:11:56.886241+00:00
-- url     : https://prove2.me/theorems/85843b67-d1b8-4d64-908a-f894c30fc361
-- title:
--   Proof of Theorem 1 (corrected: $\psi>0$; $\pi_1\ge\pi_0$ with equality on the knife-edge): the profits $\pi_0$ at $(0,0)$ and $\pi_1(\psi)$ at $(1,C_h(1))$
-- statement:
--   Throughout, $\beta\in[0,1)$ is the strength of network effects and $\rho\in[0,1)$ the users' value of data (p. 6), $P\in[0,1]$ the business's revenue model and $\psi$ the unit cost of data protection (p. 8). Let $\pi_1(\psi)=\frac1{1-\beta}\big(1+\rho+\psi-2\sqrt{\psi(1+\rho)}\big)$. Then:
--
--   1. $\Pi(0,0)=\pi_0=\frac{1-P}{1-\beta}$ for every $\psi>0$;
--   2. $\Pi(1,C_h(1))=\pi_1(\psi)$ for every $\psi>0$;
--   3. $\pi_1$ is strictly decreasing on $(0,1+\rho]$, an interval containing $(0,\psi_L]$;
--   4. for $0<\psi\le\psi_L$: $\pi_0\le\pi_1(\psi)$, with equality if and only if $P(1+\rho)=\rho$ and $\psi=P\rho$.
--
--   So for $\psi\le\psi_L$ collecting all data with protection $C_h(1)$ beats collecting nothing, strictly except on the knife-edge.
--
--   Differences from the source:
--   - correction: ψ ≥ 0 (p. 8) and the claim π1(0) > π0 → statements for ψ > 0 only; reason: C_h(1) divides by ψ; at ψ = 0 the point (1, C_h(1)) does not exist and the profit has no maximizer (β = 0, ρ = P = 1/2: Π(1, C) = 3C/(2(C + 1)) → 3/2 unattained)
--   - correction: π1(Pρ) > π0 and π1(ψL) > π0 (strict) → π₀ ≤ π₁(ψ) for 0 < ψ ≤ ψ_L, with equality iff P(1 + ρ) = ρ and ψ = Pρ; reason: π₁(ψ_L) − π₀ = (ψ_L − Pρ)/(1 − β) = (P(1 + ρ) − ρ)²/(4(1 + ρ)(1 − β)), which is 0 when P(1 + ρ) = ρ: β = 0, ρ = 1/2, P = 1/3 gives ψ_L = Pρ = 1/6 and π₁(1/6) = π₀ = 2/3
--   - generalization: π1 decreasing on ψ < Pρ and on [Pρ, ψL) (derivative 1 − √((1 + ρ)/ψ)) → StrictAntiOn on (0, 1 + ρ]; reason: ψ_L < 1 + ρ, so (0, 1 + ρ] contains both printed ranges; the printed derivative is negative on all of (0, 1 + ρ)
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_profit
import Definitions.Def_DigitalPrivacy_DataStrategy_cH
import Definitions.Def_DigitalPrivacy_DataStrategy_psiL

namespace DigitalPrivacy.DataStrategy

/-- **Proof of Theorem 1 (corrected: `ψ > 0`, `π₁ ≥ π₀` with equality on the knife-edge): the
profits `π₀` at `(0, 0)` and `π₁(ψ)` at `(1, C_h(1))`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered: "We evaluate company's profit at
both points. The first point gives π0 = (1−P)/(1−β), while the second gives π1(ψ) = (1/(1−β))(1 +
ρ + ψ − 2√(ψ(1 + ρ))) - decreasing in ψ on the interval ψ < Pρ (the derivative wrt ψ is
1 − √((1 + ρ)/ψ)). Since π1(0) > π0, … (it is also easy to verify that π1(Pρ) > π0)." Same page:
"π1(ψ) decreases with ψ on [Pρ, ψL) … Plugging ψL into π1(ψ) defined above, we get π1(ψL) > π0."

For `β, ρ ∈ [0, 1)` and `P ∈ [0, 1]`, with `π₁(ψ) = (1/(1 − β))(1 + ρ + ψ − 2√(ψ(1 + ρ)))`:

1. `Π(0, 0) = (1 − P)/(1 − β)` for every `ψ > 0`;
2. `Π(1, C_h(1)) = π₁(ψ)` for every `ψ > 0`;
3. `π₁` is strictly decreasing on `(0, 1 + ρ]` (which contains `(0, ψ_L]`);
4. for `0 < ψ ≤ ψ_L`: `π₀ ≤ π₁(ψ)`, with equality iff `P(1 + ρ) = ρ` and `ψ = Pρ`.

**Formalization Note.** `ψ > 0` replaces the page's `ψ ≥ 0` (`C_h` divides by `ψ`); the printed
"π1(0) > π0" is the limit `ψ ↓ 0` of item 4. The printed strict "π1(Pρ) > π0" and
"π1(ψL) > π0" fail when `P(1 + ρ) = ρ`, where `ψ_L = Pρ` and
`π₁(ψ_L) − π₀ = (ψ_L − Pρ)/(1 − β) = 0`; item 4 states the inequality weakly with its exact
equality case. -/
theorem proof_thm1_pi0_pi1 {β ρ P : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    (∀ ψ : ℝ, 0 < ψ → profit β ρ P ψ 0 0 = (1 - P) / (1 - β)) ∧
    (∀ ψ : ℝ, 0 < ψ → profit β ρ P ψ 1 (cH β ρ P ψ 1) =
      (1 / (1 - β)) * (1 + ρ + ψ - 2 * Real.sqrt (ψ * (1 + ρ)))) ∧
    StrictAntiOn (fun ψ : ℝ => (1 / (1 - β)) * (1 + ρ + ψ - 2 * Real.sqrt (ψ * (1 + ρ))))
      (Set.Ioc 0 (1 + ρ)) ∧
    (∀ ψ : ℝ, 0 < ψ → ψ ≤ psiL ρ P →
      (1 - P) / (1 - β) ≤ (1 / (1 - β)) * (1 + ρ + ψ - 2 * Real.sqrt (ψ * (1 + ρ))) ∧
      ((1 - P) / (1 - β) = (1 / (1 - β)) * (1 + ρ + ψ - 2 * Real.sqrt (ψ * (1 + ρ))) ↔
        P * (1 + ρ) = ρ ∧ ψ = P * ρ)) := by sorry

end DigitalPrivacy.DataStrategy
