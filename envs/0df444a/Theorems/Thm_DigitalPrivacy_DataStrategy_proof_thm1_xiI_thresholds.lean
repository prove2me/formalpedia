-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_proof_thm1_xiI_thresholds
-- name    : DigitalPrivacy.DataStrategy.proof_thm1_xiI_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:12:33.907302+00:00
-- url     : https://prove2.me/theorems/c3700647-9cbc-4cc4-ab03-25df8a46a150
-- title:
--   Proof of Theorem 1, case $\psi>P\rho$ (corrected: weak threshold order): $\xi_i$ solves $C_{{inv}}=C_h$, is $0$ at $\psi_H$, $1$ at $\psi_L$, and decreasing in $\psi$
-- statement:
--   Throughout, $\beta\in[0,1)$ is the strength of network effects and $\rho\in[0,1)$ the users' value of data (p. 6), $P\in[0,1]$ the business's revenue model and $\psi$ the unit cost of data protection (p. 8). Assume $P\rho>0$. Then:
--
--   1. for $\psi>P\rho$ and $\xi>0$: $C_{inv}(\xi)=C_h(\xi)$ if and only if $\xi=\xi_i(\psi)$, where
--   $$\xi_i=\frac1{2P\rho}\Big(-(1-P)\rho-P+|P-(1-P)\rho|\sqrt{\tfrac{\psi}{\psi-P\rho}}\Big);$$
--   2. $P\rho\le\psi_L$, with equality if and only if $P(1+\rho)=\rho$; if $P<1$, also $\psi_L\le\psi_H$, with equality if and only if $P(1+\rho)=\rho$;
--   3. if $P(1+\rho)\ne\rho$: $\xi_i(\psi_L)=1$ and $\psi\mapsto\xi_i(\psi)$ is strictly decreasing on $\psi>P\rho$; if moreover $P<1$, then $\xi_i(\psi_H)=0$.
--
--   These facts sort the protection costs above $P\rho$ into the regions where the interior root lies above $1$, in $(0,1)$, or below $0$.
--
--   Differences from the source:
--   - encoding: the formulas quoted with 1/(2Pρ) and ψ_H = (P + (1 − P)ρ)²/(4(1 − P)) → hypothesis 0 < Pρ, and P < 1 in the clauses that use ψ_H; reason: they only exclude parameters at which the quoted formulas are undefined (division by zero)
--   - correction: ψL > Pρ, ψH > Pρ and ψH > ψL (strict) → Pρ ≤ ψ_L and (for P < 1) ψ_L ≤ ψ_H, each with equality iff P(1 + ρ) = ρ; reason: ψ_L − Pρ = (P(1 + ρ) − ρ)²/(4(1 + ρ)) and ψ_H − ψ_L = (P + ρ)(P(1 + ρ) − ρ)²/(4(1 − P)(1 + ρ)); at ρ = 1/2, P = 1/3 all three equal 1/6
--   - reading: two non-negative roots: ξ = 0 and ξi → for ξ > 0: C_inv(ξ) = C_h(ξ) iff ξ = ξᵢ; reason: ξ = 0 is the trivial common root; the iff states that ξᵢ is the only other root (when ξᵢ ≤ 0 there is no positive one)
--   - reading: ξi > 0 when ψ ∈ [Pρ, ψH], ξi < 1 when ψ > ψL, ξi decreases with ψ, argued for the case P > (1 − P)ρ → for P(1 + ρ) ≠ ρ: ξᵢ(ψ_L) = 1, StrictAntiOn on ψ > Pρ, and ξᵢ(ψ_H) = 0 when P < 1; reason: the proof says the case P < (1 − P)ρ is similar; the values at the thresholds and strict decrease give the printed sign conditions
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_cInv
import Definitions.Def_DigitalPrivacy_DataStrategy_cH
import Definitions.Def_DigitalPrivacy_DataStrategy_xiI
import Definitions.Def_DigitalPrivacy_DataStrategy_psiL
import Definitions.Def_DigitalPrivacy_DataStrategy_psiH

namespace DigitalPrivacy.DataStrategy

/-- **Proof of Theorem 1, case `ψ > Pρ` (corrected: thresholds weakly ordered, equal on
`P(1 + ρ) = ρ`): `ξᵢ` solves `C_inv = C_h`, vanishes at `ψ_H`, equals `1` at `ψ_L` and decreases
in `ψ`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 30 (PDF 31), unnumbered: "Case ψ > Pρ: Solve Cinv(ξ) =
Ch(ξ). We get two non-negative roots: ξ = 0 and ξi = (1/(2Pρ))(−(1−P)ρ − P + |P − (1−P)ρ|
√(ψ/(ψ−Pρ))). … ξi > 0 when ψ ∈ [Pρ, ψH], where ψH = (P+(1−P)ρ)²/(4(1−P)) is a solution to
ξi = 0 wrt ψ. Similarly, ξi < 1 when ψ > ψL, where ψL = (P+ρ+Pρ)²/(4(1+ρ)) is a solution to
ξi = 1 wrt ψ. Both ψL > Pρ and ψH > Pρ, also ψH > ψL (ξi decreases with ψ)."

For `β, ρ ∈ [0, 1)`, `P ∈ [0, 1]` and `Pρ > 0`:

1. for `ψ > Pρ` and `ξ > 0`: `C_inv(ξ) = C_h(ξ)` iff `ξ = ξᵢ(ψ)`;
2. `Pρ ≤ ψ_L`, with equality iff `P(1 + ρ) = ρ`; if `P < 1`, also `ψ_L ≤ ψ_H`, with equality
   iff `P(1 + ρ) = ρ`;
3. if `P(1 + ρ) ≠ ρ`: `ξᵢ(ψ_L) = 1`, `ξᵢ` is strictly decreasing on `ψ > Pρ`, and, if `P < 1`,
   `ξᵢ(ψ_H) = 0`.

**Formalization Note.** `Pρ > 0` only excludes the cases where the quoted `1/(2Pρ)` is
undefined; `P < 1` is assumed only in the clauses that use `ψ_H`, which is `+∞` at `P = 1`. The printed strict "ψL > Pρ", "ψH > Pρ", "ψH > ψL" fail when
`P(1 + ρ) = ρ`: `ψ_L − Pρ = (P(1+ρ) − ρ)²/(4(1+ρ))` and
`ψ_H − ψ_L = (P + ρ)(P(1+ρ) − ρ)²/(4(1−P)(1+ρ))`. There `|P − (1 − P)ρ| = 0` and `ξᵢ` is constant. -/
theorem proof_thm1_xiI_thresholds {β ρ P : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hPρ : 0 < P * ρ) :
    (∀ ψ : ℝ, P * ρ < ψ → ∀ ξ : ℝ, 0 < ξ →
      (cInv β ρ P ξ = cH β ρ P ψ ξ ↔ ξ = xiI ρ P ψ)) ∧
    P * ρ ≤ psiL ρ P ∧ (P * ρ = psiL ρ P ↔ P * (1 + ρ) = ρ) ∧
    (P < 1 → psiL ρ P ≤ psiH ρ P ∧ (psiL ρ P = psiH ρ P ↔ P * (1 + ρ) = ρ)) ∧
    (P * (1 + ρ) ≠ ρ →
      xiI ρ P (psiL ρ P) = 1 ∧ StrictAntiOn (xiI ρ P) (Set.Ioi (P * ρ)) ∧
      (P < 1 → xiI ρ P (psiH ρ P) = 0)) := by sorry

end DigitalPrivacy.DataStrategy
