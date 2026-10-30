-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_proof_thm1_summary
-- name    : DigitalPrivacy.DataStrategy.proof_thm1_summary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:13:56.723333+00:00
-- url     : https://prove2.me/theorems/13e9c745-474f-439f-9378-c030e5e0cf28
-- title:
--   Proof of Theorem 1, summary (corrected: $\psi>0$, $P\rho=0$, knife-edge excluded): the optimum is $(1,C_h(1))$, $(\xi_i,C_h(\xi_i))$ or $(0,0)$ by the region of $\psi$
-- statement:
--   Throughout, $\beta\in[0,1)$ is the strength of network effects and $\rho\in[0,1)$ the users' value of data (p. 6), $P\in[0,1]$ the business's revenue model and $\psi$ the unit cost of data protection (p. 8). Assume $\psi>0$, and exclude the knife-edge $P(1+\rho)=\rho$, $\psi=P\rho$. Then $P\rho\le\psi_L$, $\psi_L\le\psi_H$ when $P<1$, and:
--
--   1. if $\psi\le\psi_L$, the unique optimal data strategy is $(1,C_h(1))$;
--   2. if $\psi_L<\psi$ and $4(1-P)\psi<(P+(1-P)\rho)^2$ (that is, $\psi<\psi_H$), then $\xi_i\in(0,1)$ and the unique optimal data strategy is $(\xi_i,C_h(\xi_i))$;
--   3. if $(P+(1-P)\rho)^2\le4(1-P)\psi$ (that is, $\psi\ge\psi_H$), the unique optimal data strategy is $(0,0)$.
--
--   Here $\xi_i$ is the interior root, extended to $P\rho=0$. The three cases combine into displays (5)–(6) of Theorem 1.
--
--   Differences from the source:
--   - correction: ψ ≥ 0 (p. 8) → 0 < ψ; reason: C_h and (6) divide by ψ, and at ψ = 0 with P + ρ > 0 the profit has no maximizer: β = 0, ρ = P = 1/2, ψ = 0 gives Π(1, C) = 3C/(2(C + 1)), which tends to 3/2 = sup Π without reaching it
--   - correction: the factor 1/(2Pρ) in ξᵢ and in (5), undefined at P = 0 and at ρ = 0 → xiI: for Pρ = 0 the root (a² − 4ψ(1 − P))/(4aψ), a = P + (1 − P)ρ, of the same equation C_inv = C_h (linear there), and 0 when P = ρ = 0; reason: the literal formula with Lean's x/0 = 0 gives ξ* = 0 at β = 0, ρ = 1/2, P = 0, ψ = 1/100, where the optimum is ξ* = 1; the replacement is also the limit of the printed formula as Pρ → 0
--   - correction: cases (i) and (iii) for all ψ → the knife-edge P(1 + ρ) = ρ, ψ = Pρ is excluded; reason: there Pρ = ψ_L = ψ_H, so (i) prescribes (1, C_h(1)) and (iii) prescribes (0, 0); in fact the optimal set is the whole segment {(ξ, C_h(ξ)) : ξ ∈ [0, 1]} (β = 0, ρ = 1/2, P = 1/3, ψ = 1/6: Π(ξ, 2ξ) = 2/3 for all ξ ∈ [0, 1])
--   - correction: two thresholds Pρ < ψL ≤ ψH → Pρ ≤ ψ_L, and ψ_L ≤ ψ_H for P < 1; reason: ψ_L − Pρ = (P(1 + ρ) − ρ)²/(4(1 + ρ)) vanishes when P(1 + ρ) = ρ (ρ = 1/2, P = 1/3: ψ_L = Pρ = 1/6)
--   - encoding: ψ ∈ (ψL, ψH) and ψ ≥ ψH → 4(1 − P)ψ < (P + (1 − P)ρ)² and (P + (1 − P)ρ)² ≤ 4(1 − P)ψ; reason: equivalent for P < 1; at P = 1, where ψ_H = +∞, the first always holds and the second never does, as in the source
--   - reading: then ξ⋆ = …, C⋆ = … → the set of optimal data strategies is exactly that point; reason: the summary names the business's choice; the iff says it is the unique maximizer
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 31 (PDF 32), unnumbered

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_IsBusinessOptimal
import Definitions.Def_DigitalPrivacy_DataStrategy_cH
import Definitions.Def_DigitalPrivacy_DataStrategy_xiI
import Definitions.Def_DigitalPrivacy_DataStrategy_psiL
import Definitions.Def_DigitalPrivacy_DataStrategy_psiH

namespace DigitalPrivacy.DataStrategy

/-- **Proof of Theorem 1, summary (corrected: `ψ > 0`, `Pρ = 0` extension, knife-edge excluded):
the optimum is `(1, C_h(1))`, `(ξᵢ, C_h(ξᵢ))` or `(0, 0)` according to `ψ ≤ ψ_L`,
`ψ_L < ψ < ψ_H`, `ψ ≥ ψ_H`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), proof of Theorem 1 (App. A.2), p. 31 (PDF 32), unnumbered: "Summarizing the above, we have
two thresholds Pρ < ψL ≤ ψH such that: (i) if ψ ≤ ψL, then ξ⋆ = 1 and C⋆ = Ch(1); (ii) if ψ ∈
(ψL, ψH), then ξ⋆ = ξi = (1/(2Pρ))(−(1 − P)ρ − P + |P − (1 − P)ρ|√(ψ/(ψ−Pρ))) ∈ (0, 1) and
C⋆ = Ch(ξi); (iii) if ψ ≥ ψH, then ξ⋆ = 0 and C⋆ = 0. Here function Ch(ξ) is defined in Lemma 1."

For `β, ρ ∈ [0, 1)`, `P ∈ [0, 1]`, `ψ > 0`, and not both `P(1 + ρ) = ρ` and `ψ = Pρ`:

0. `Pρ ≤ ψ_L`, and `ψ_L ≤ ψ_H` when `P < 1`;
1. if `ψ ≤ ψ_L`, the optimal data strategies are exactly `(1, C_h(1))`;
2. if `ψ_L < ψ` and `4(1 − P)ψ < (P + (1 − P)ρ)²` (i.e. `ψ < ψ_H`), then `ξᵢ ∈ (0, 1)` and the
   optimal data strategies are exactly `(ξᵢ, C_h(ξᵢ))`;
3. if `(P + (1 − P)ρ)² ≤ 4(1 − P)ψ` (i.e. `ψ ≥ ψ_H`), the optimal data strategy is exactly `(0, 0)`.

**Formalization Note.** `ψ > 0` replaces the page's `ψ ≥ 0` (at `ψ = 0` there is no optimum
once `P + ρ > 0`). `ξᵢ` is `xiI`, extended to `Pρ = 0` (the printed `1/(2Pρ)` is undefined at
`P = 0` and at `ρ = 0`). `ψ ≥ ψ_H` is written `(P + (1 − P)ρ)² ≤ 4(1 − P)ψ`, so that at `P = 1`
(`ψ_H = +∞`) region 3 is empty. On the knife-edge `P(1 + ρ) = ρ`, `ψ = Pρ` (where
`Pρ = ψ_L = ψ_H`) cases (i) and (iii) both apply and contradict each other: there the optimal set
is a segment (see the goal theorem), so it is excluded here. "Pρ < ψL" is weak in general and
strict off `P(1 + ρ) = ρ` (item 0). -/
theorem proof_thm1_summary {β ρ P ψ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ) (hke : ¬ (P * (1 + ρ) = ρ ∧ ψ = P * ρ)) :
    (P * ρ ≤ psiL ρ P ∧ (P < 1 → psiL ρ P ≤ psiH ρ P)) ∧
    (ψ ≤ psiL ρ P →
      ∀ ξ C : ℝ, IsBusinessOptimal β ρ P ψ ξ C ↔ ξ = 1 ∧ C = cH β ρ P ψ 1) ∧
    (psiL ρ P < ψ → 4 * (1 - P) * ψ < (P + (1 - P) * ρ) ^ 2 →
      xiI ρ P ψ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ ξ C : ℝ, IsBusinessOptimal β ρ P ψ ξ C ↔
        ξ = xiI ρ P ψ ∧ C = cH β ρ P ψ (xiI ρ P ψ)) ∧
    ((P + (1 - P) * ρ) ^ 2 ≤ 4 * (1 - P) * ψ →
      ∀ ξ C : ℝ, IsBusinessOptimal β ρ P ψ ξ C ↔ ξ = 0 ∧ C = 0) := by sorry

end DigitalPrivacy.DataStrategy
