-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_proof_thm1_cInv
-- name    : DigitalPrivacy.DataStrategy.proof_thm1_cInv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:10:42.47708+00:00
-- url     : https://prove2.me/theorems/1c32eb22-760b-443b-ae14-3c1c93025a03
-- title:
--   Proof of Theorem 1: Lemma 2's interior root is increasing and concave in $C$, with inverse $C_{{inv}}$
-- statement:
--   Throughout, $\beta\in[0,1)$ is the strength of network effects and $\rho\in[0,1)$ the users' value of data (p. 6), $P\in[0,1]$ the business's revenue model and $\psi$ the unit cost of data protection (p. 8). Assume $P+(1-P)\rho>0$. Then $C\mapsto-\kappa(C)+\sqrt{\kappa(C)^2+C(1-\beta)}$ is strictly increasing and concave on $C\ge0$, and for $\xi\ge0$, $C\ge0$:
--
--   $$-\kappa(C)+\sqrt{\kappa(C)^2+C(1-\beta)}=\xi\iff C=C_{inv}(\xi)=\frac1{1-\beta}\cdot\frac{\xi[(P+(1-P)\rho)\xi+2(1-P)]}{P+(1-P)\rho+2\xi P\rho} .$$
--
--   So Lemma 2's best-response curve can be written as $C=C_{inv}(\xi)$ and compared with Lemma 1's $C=C_h(\xi)$.
--
--   Differences from the source:
--   - encoding: κ(C), C_l and C_inv, which divide by P + (1 − P)ρ → hypothesis 0 < P + (1 − P)ρ; reason: it only excludes P = ρ = 0, where those formulas are undefined
--   - reading: C_inv(ξ) is the solution to −κ(C) + √(κ(C)² + C(1 − β)) = ξ wrt C → for ξ ≥ 0 and C ≥ 0: the equation holds iff C = C_inv(ξ); reason: the iff states both that C_inv(ξ) solves the equation and that it is its only nonnegative solution
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 29 (PDF 30), unnumbered

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_xiOfC
import Definitions.Def_DigitalPrivacy_DataStrategy_cInv

namespace DigitalPrivacy.DataStrategy

/-- **Proof of Theorem 1: Lemma 2's interior root is increasing and concave in `C`, with inverse `C_inv`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 29 (PDF 30), unnumbered: "We know that −κ(C) +
√(κ(C)² + C(1 − β)) is increasing and concave in C. Denote Cinv(ξ) solution to −κ(C) + √(κ(C)² +
C(1 − β)) = ξ wrt C (here κ(C) is defined in Lemma 2). We have that: Cinv(ξ) = 1/(1 − β) ·
ξ[(P + (1 − P)ρ)ξ + 2(1 − P)]/(P + (1 − P)ρ + 2ξPρ)."

For `β, ρ ∈ [0, 1)`, `P ∈ [0, 1]` and `P + (1 − P)ρ > 0`: `C ↦ ξ⋆(C)` is strictly increasing and concave on `C ≥ 0`, and
for `ξ ≥ 0`, `C ≥ 0`: `ξ⋆(C) = ξ` iff `C = C_inv(ξ)`.

**Formalization Note.** `P + (1 − P)ρ > 0` only excludes
`P = ρ = 0`, where `κ` and `C_inv` divide by zero. -/
theorem proof_thm1_cInv {β ρ P : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (ha : 0 < P + (1 - P) * ρ) :
    StrictMonoOn (xiOfC β ρ P) (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) (xiOfC β ρ P) ∧
    ∀ ξ C : ℝ, 0 ≤ ξ → 0 ≤ C → (xiOfC β ρ P C = ξ ↔ C = cInv β ρ P ξ) := by sorry

end DigitalPrivacy.DataStrategy
