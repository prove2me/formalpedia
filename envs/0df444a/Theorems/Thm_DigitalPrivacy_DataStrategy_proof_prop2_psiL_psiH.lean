-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_proof_prop2_psiL_psiH
-- name    : DigitalPrivacy.DataStrategy.proof_prop2_psiL_psiH
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:14:33.325893+00:00
-- url     : https://prove2.me/theorems/72e3e6f6-8829-4d30-b578-d2faded23ca2
-- title:
--   Proof of Proposition 2 (A.3): $\psi_L,\psi_H$ are increasing and convex in $P$, $\psi_H\ge\psi_L$ with contact only at $P=\rho/(1+\rho)$
-- statement:
--   Let $\rho\in[0,1)$ and regard $\psi_L=\frac{(P+\rho+P\rho)^2}{4(1+\rho)}$ and $\psi_H=\frac{(P+(1-P)\rho)^2}{4(1-P)}$ as functions of the revenue model $P$. Then:
--
--   1. $P\mapsto\psi_L$ is strictly increasing and convex on $[0,1]$;
--   2. $P\mapsto\psi_H$ is strictly increasing and convex on $[0,1)$;
--   3. for $P\in[0,1)$, $\psi_L\le\psi_H$, with equality if and only if $P=\rho/(1+\rho)$, where $\psi_L=\rho^2/(1+\rho)$;
--   4. $\psi_L(0)=\frac{\rho^2}{4(1+\rho)}$ and $\psi_H(0)=\frac{\rho^2}4$.
--
--   These threshold facts underlie the monotonicity of $\xi^\star$ and $C^\star$ in $P$ claimed in Theorem 1.
--
--   Differences from the source:
--   - encoding: ψH as a function of P on [0, 1] → statements about ψ_H on [0, 1); reason: ψ_H = +∞ at P = 1 (division by 4(1 − P) = 0)
--   - reading: ψL, ψH are increasing functions of P → StrictMonoOn; reason: both are strictly increasing; the strict reading is the stronger one
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), App. A.3, p. 32 (PDF 33), unnumbered

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_psiL
import Definitions.Def_DigitalPrivacy_DataStrategy_psiH

namespace DigitalPrivacy.DataStrategy

/-- **Proof of Proposition 2 (A.3): `ψ_L`, `ψ_H` are increasing and convex in `P`, `ψ_H ≥ ψ_L`
with contact only at `P = ρ/(1 + ρ)`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), App. A.3, p. 32 (PDF 33), unnumbered: "It is easy to verify that both ψL, ψH are increasing,
convex functions of P. Furthermore, ψH ≥ ψL and they intersect only at one point P = ρ/(1+ρ) for
P ∈ [0, 1] where ψL = ψH = ρ²/(1+ρ). At P = 0 we have ψL(P = 0) = ρ²/(4(1+ρ)) and
ψH(P = 0) = ρ²/4." Appendix A.2 (p. 31) defers the monotonicity of `ξ*`, `C*` in `P` to this
analysis.

For `ρ ∈ [0, 1)`:

1. `P ↦ ψ_L` is strictly increasing and convex on `[0, 1]`;
2. `P ↦ ψ_H` is strictly increasing and convex on `[0, 1)`;
3. for `P ∈ [0, 1)`: `ψ_L ≤ ψ_H`, with equality iff `P = ρ/(1 + ρ)`; and `ψ_L(ρ/(1 + ρ)) = ρ²/(1 + ρ)`;
4. `ψ_L(0) = ρ²/(4(1 + ρ))` and `ψ_H(0) = ρ²/4`.

**Formalization Note.** "Increasing" is stated strictly. `ψ_H` is stated on `[0, 1)`: at `P = 1`
it is `+∞`. -/
theorem proof_prop2_psiL_psiH {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    StrictMonoOn (fun P => psiL ρ P) (Set.Icc 0 1) ∧
    ConvexOn ℝ (Set.Icc 0 1) (fun P => psiL ρ P) ∧
    StrictMonoOn (fun P => psiH ρ P) (Set.Ico 0 1) ∧
    ConvexOn ℝ (Set.Ico 0 1) (fun P => psiH ρ P) ∧
    (∀ P ∈ Set.Ico (0 : ℝ) 1, psiL ρ P ≤ psiH ρ P ∧ (psiL ρ P = psiH ρ P ↔ P = ρ / (1 + ρ))) ∧
    psiL ρ (ρ / (1 + ρ)) = ρ ^ 2 / (1 + ρ) ∧
    psiL ρ 0 = ρ ^ 2 / (4 * (1 + ρ)) ∧ psiH ρ 0 = ρ ^ 2 / 4 := by sorry

end DigitalPrivacy.DataStrategy
