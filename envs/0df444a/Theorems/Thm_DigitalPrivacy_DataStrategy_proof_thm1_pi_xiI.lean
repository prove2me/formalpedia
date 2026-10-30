-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_proof_thm1_pi_xiI
-- name    : DigitalPrivacy.DataStrategy.proof_thm1_pi_xiI
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:14.007306+00:00
-- url     : https://prove2.me/theorems/5c9bc372-7720-43ad-9339-a85ba77b52c9
-- title:
--   Proof of Theorem 1 (corrected: factor $1/(1-\beta)$, both signs of $P-(1-P)\rho$): the profit at $(\xi_i,C_h(\xi_i))$ decreases on $[\psi_L,\psi_H]$ to $\pi_0$
-- statement:
--   Throughout, $\beta\in[0,1)$ is the strength of network effects and $\rho\in[0,1)$ the users' value of data (p. 6), $P\in[0,1]$ the business's revenue model and $\psi$ the unit cost of data protection (p. 8). Assume $P<1$, $P\rho>0$ and $P(1+\rho)\ne\rho$. Let $z(\psi)=\sqrt{\psi/(\psi-P\rho)}$, $d=|P-(1-P)\rho|$ and $\pi_{\xi_i}(\psi)=\Pi(\xi_i,C_h(\xi_i))$. Then:
--
--   1. for $\psi\in[\psi_L,\psi_H]$,
--   $$\pi_{\xi_i}(\psi)=\frac1{1-\beta}\cdot\frac{\psi}{4P^2\rho^2}\Big[P+(1-P)\rho+P\rho\,d\,\frac{z(\psi)}{\psi}-d\,z(\psi)\Big]^2;$$
--   2. $\pi_{\xi_i}$ is strictly decreasing on $[\psi_L,\psi_H]$;
--   3. $\pi_{\xi_i}(\psi_H)=\frac{1-P}{1-\beta}=\pi_0$.
--
--   So on $[\psi_L,\psi_H)$ the interior point beats $(0,0)$.
--
--   Differences from the source:
--   - encoding: the formulas quoted with 1/(2Pρ) and ψ_H = (P + (1 − P)ρ)²/(4(1 − P)) → hypotheses 0 < Pρ and P < 1; reason: they only exclude parameters at which the quoted formulas are undefined (division by zero)
--   - encoding: the proof's two cases P > (1 − P)ρ and P < (1 − P)ρ → hypothesis P(1 + ρ) ≠ ρ; reason: P(1 + ρ) = ρ is P = (1 − P)ρ, where [ψ_L, ψ_H] = {Pρ} and z(ψ) = √(ψ/(ψ − Pρ)) is undefined
--   - correction: πξi(ψ) = (ψ/(4P²ρ²))[P + (1 − P)ρ + Pρ(P − (1 − P)ρ)z(ψ)/ψ − Pz(ψ) + (1 − P)ρz(ψ)]² → the same with the factor 1/(1 − β) and with |P − (1 − P)ρ| in place of P − (1 − P)ρ in both occurrences; reason: the printed form contradicts the page's own πξi(ψH) = (1−P)/(1−β) for β ≠ 0, and for P < (1 − P)ρ it is false: β = 0, P = 0.149, ρ = 0.416, ψ = ψ_L ≈ 0.0694 gives printed ≈ 1.468 against the true profit ≈ 0.858; when P > (1 − P)ρ and β = 0 it is the printed form
--   - reading: πξi(ψ) > π0 on ψ ∈ [ψL, ψH], checked at ψH → π_ξᵢ strictly decreasing on [ψ_L, ψ_H] with π_ξᵢ(ψ_H) = π₀; reason: the page itself gives π_ξᵢ(ψ_H) = π₀ and a negative derivative, so the strict inequality holds on [ψ_L, ψ_H) and is an equality at ψ_H
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 31 (PDF 32), unnumbered

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_profit
import Definitions.Def_DigitalPrivacy_DataStrategy_cH
import Definitions.Def_DigitalPrivacy_DataStrategy_xiI
import Definitions.Def_DigitalPrivacy_DataStrategy_psiL
import Definitions.Def_DigitalPrivacy_DataStrategy_psiH

namespace DigitalPrivacy.DataStrategy

/-- **Proof of Theorem 1 (corrected: factor `1/(1 − β)`, both signs of `P − (1 − P)ρ`): the
profit at `(ξᵢ, C_h(ξᵢ))` decreases on `[ψ_L, ψ_H]` to `π₀`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 31 (PDF 32), unnumbered: "Finally, on the interval
ψ ∈ [ψL, ψH], there are two points of intersection of the best-responses: ξ = 0, C = 0 (delivering
profit π0) and ξ = ξi ∈ [0, 1], C = Ch(ξi) with profit: πξi(ψ) = (ψ/(4P²ρ²))[P + (1 − P)ρ +
Pρ(P − (1 − P)ρ)z(ψ)/ψ − Pz(ψ) + (1 − P)ρz(ψ)]² Where z(ψ) = √(ψ/(ψ−Pρ)) - decreasing function
of ψ. … To check that πξi(ψ) > π0 on ψ ∈ [ψL, ψH] we thus need to check this inequality at ψH.
It is easy to verify that πξi(ψH) = (1−P)/(1−β) = π0."

For `β, ρ ∈ [0, 1)`, `0 ≤ P < 1`, `Pρ > 0` and `P(1 + ρ) ≠ ρ`, with `z(ψ) = √(ψ/(ψ − Pρ))`,
`d = |P − (1 − P)ρ|` and `π_ξᵢ(ψ) = Π(ξᵢ(ψ), C_h(ξᵢ(ψ)))`:

1. for `ψ ∈ [ψ_L, ψ_H]`:
   `π_ξᵢ(ψ) = (1/(1 − β))·(ψ/(4P²ρ²))·[P + (1 − P)ρ + Pρ·d·z(ψ)/ψ − d·z(ψ)]²`;
2. `π_ξᵢ` is strictly decreasing on `[ψ_L, ψ_H]`;
3. `π_ξᵢ(ψ_H) = (1 − P)/(1 − β)`.

**Formalization Note.** The printed closed form lacks the factor `1/(1 − β)` (it contradicts the
same page's `πξi(ψH) = (1−P)/(1−β)` when `β ≠ 0`), and it is written for the proof's case
`P > (1 − P)ρ`: for `P < (1 − P)ρ` it is wrong (`β = 0`, `P = 0.149`, `ρ = 0.416`, `ψ = ψ_L ≈ 0.0694`:
printed ≈ 1.468, true ≈ 0.858). Item 1 uses `d = |P − (1 − P)ρ|` in both occurrences, which
is the printed form when `P > (1 − P)ρ`. `P(1 + ρ) ≠ ρ` (`P ≠ (1 − P)ρ`) is the proof's case
split; on `P(1 + ρ) = ρ` the interval `[ψ_L, ψ_H]` is the single point `Pρ`, where `z` is
undefined. -/
theorem proof_thm1_pi_xiI {β ρ P : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP0 : 0 ≤ P) (hP1 : P < 1) (hPρ : 0 < P * ρ) (hke : P * (1 + ρ) ≠ ρ) :
    (∀ ψ ∈ Set.Icc (psiL ρ P) (psiH ρ P),
      profit β ρ P ψ (xiI ρ P ψ) (cH β ρ P ψ (xiI ρ P ψ)) =
        (1 / (1 - β)) * (ψ / (4 * P ^ 2 * ρ ^ 2)) *
          (P + (1 - P) * ρ + P * ρ * |P - (1 - P) * ρ| * Real.sqrt (ψ / (ψ - P * ρ)) / ψ
            - |P - (1 - P) * ρ| * Real.sqrt (ψ / (ψ - P * ρ))) ^ 2) ∧
    StrictAntiOn (fun ψ => profit β ρ P ψ (xiI ρ P ψ) (cH β ρ P ψ (xiI ρ P ψ)))
      (Set.Icc (psiL ρ P) (psiH ρ P)) ∧
    profit β ρ P (psiH ρ P) (xiI ρ P (psiH ρ P)) (cH β ρ P (psiH ρ P) (xiI ρ P (psiH ρ P))) =
      (1 - P) / (1 - β) := by sorry

end DigitalPrivacy.DataStrategy
