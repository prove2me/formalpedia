-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_proof_thm1_case_psi_lt_Prho
-- name    : DigitalPrivacy.DataStrategy.proof_thm1_case_psi_lt_Prho
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:11:09.45947+00:00
-- url     : https://prove2.me/theorems/d1f097bd-fd4b-4325-87c1-e402ad7842a3
-- title:
--   Proof of Theorem 1, case $\psi<P\rho$ (corrected: $\psi>0$): $C_{{inv}}(\xi)<C_h(\xi)$ for every $\xi>0$
-- statement:
--   Throughout, $\beta\in[0,1)$ is the strength of network effects and $\rho\in[0,1)$ the users' value of data (p. 6), $P\in[0,1]$ the business's revenue model and $\psi$ the unit cost of data protection (p. 8). If $0<\psi<P\rho$, then
--
--   $$C_{inv}(\xi)<C_h(\xi)\qquad\text{for every }\xi>0 .$$
--
--   Hence the two best-response curves meet only at $\xi=0$, and on $[0,1]$ the candidate optima are $(0,0)$ and $(1,C_h(1))$.
--
--   Differences from the source:
--   - correction: ψ ≥ 0 (p. 8), so the case ψ < Pρ includes ψ = 0 → 0 < ψ < Pρ; reason: C_h divides by ψ and is undefined at ψ = 0; at ψ = 0 the profit has no maximizer (β = 0, ρ = P = 1/2: Π(1, C) = 3C/(2(C + 1)) → 3/2 unattained)
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), pp. 29–30 (PDF 30–31), unnumbered

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_cInv
import Definitions.Def_DigitalPrivacy_DataStrategy_cH

namespace DigitalPrivacy.DataStrategy

/-- **Proof of Theorem 1, case `ψ < Pρ` (corrected: `ψ > 0`): `C_inv(ξ) < C_h(ξ)` for every `ξ > 0`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), pp. 29–30 (PDF 30–31), unnumbered: "Case ψ < Pρ: We first
show that Cinv(ξ) < Ch(ξ) (where Ch(ξ) is defined in Lemma 1) and they only intersect at ξ = 0
under this condition. … It is easy to check that inequality holds in this case and hence
Cinv(ξ) < Ch(ξ), ∀ξ > 0."

For `β, ρ ∈ [0, 1)`, `P ∈ [0, 1]` and `0 < ψ < Pρ`: `C_inv(ξ) < C_h(ξ)` for every `ξ > 0`.

**Formalization Note.** The page allows `ψ ≥ 0` (p. 8); `C_h` divides by `ψ`, so `ψ = 0` is
excluded. -/
theorem proof_thm1_case_psi_lt_Prho {β ρ P ψ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ0 : 0 < ψ) (hψ : ψ < P * ρ) :
    ∀ ξ : ℝ, 0 < ξ → cInv β ρ P ξ < cH β ρ P ψ ξ := by sorry

end DigitalPrivacy.DataStrategy
