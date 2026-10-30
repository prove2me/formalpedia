-- Prove2me | Theorems.Thm_BBPSSW_Distill_recurrence_step
-- name    : BBPSSW.Distill.recurrence_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:47:12.749997+00:00
-- url     : https://prove2.me/theorems/ed0da02f-fe21-4a2d-a81c-bd17f9819f98
-- title:
--   One recurrence step: success probability $>1/4$ and fidelity $F'$, Eq. (7)
-- statement:
--   Let $0\le F\le1$. Apply steps A1–A2 (and the $\sigma_y$ rotation of A3) to two Werner pairs $W_F\otimes W_F$, the first being the source, and let $K$ be the unnormalized state of the kept source pair (`recurrenceKept`). Let
--
--   $$p=F^2+\tfrac23F(1-F)+\tfrac59(1-F)^2 .$$
--
--   Then
--
--   1. the probability that the source pair is kept is $\mathrm{tr}\,K=p$;
--   2. $p>\tfrac14$;
--   3. the kept pair has singlet fidelity
--
--   $$\Big\langle\Psi^-\Big|\frac{K}{p}\Big|\Psi^-\Big\rangle=F'(F)=\frac{F^2+\frac19(1-F)^2}{F^2+\frac23F(1-F)+\frac59(1-F)^2}.$$
--
--   After the random bilateral rotation of A3 the kept pair is therefore the Werner state $W_{F'}$.
--
--   Differences from the source:
--   - generalization: two Werner pairs of fidelity F > 1/2 → every F with 0 ≤ F ≤ 1; reason: the identities hold on the whole range of Werner states and specialize to F > 1/2
--   - reading: one Werner pair of fidelity F′ → the kept pair (before the final random bilateral rotation) has singlet fidelity F′; reason: that rotation leaves the singlet fidelity unchanged and produces W_F′; F′ > F is stated in recurrenceMap_iterate
--   - encoding: a unilateral σy rotation on each pair (side not named) → σy on Alice's spin of each pair (A1) and of the kept pair (A3); reason: σy on Bob's spin maps each Bell state to the same Bell state up to a phase, so the resulting density matrix is the same
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, pp. 2–3, Eq. (7) and steps A1–A3

import Mathlib
import Definitions.Def_BBPSSW_Distill_wernerState
import Definitions.Def_BBPSSW_Distill_singletFidelity
import Definitions.Def_BBPSSW_Distill_recurrenceKept
import Definitions.Def_BBPSSW_Distill_recurrenceMap

namespace BBPSSW.Distill

/-- **One recurrence step: success probability and output fidelity, Eq. (7).**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, pp. 2–3: "We now show that, given two Werner pairs of fidelity F > 1/2, Alice and Bob
can use local operations and two-way classical communication to obtain, with probability
greater than 1/4, one Werner pair of fidelity F′ > F, where the F′ satisfies the recurrence
relation F′ = (F^2 + (1/9)(1−F)^2) / (F^2 + (2/3)F(1−F) + (5/9)(1−F)^2). (7)", with the protocol
A1–A3.

For `0 ≤ F ≤ 1`, run steps A1–A2 (and the σy of A3) on two Werner pairs `W_F ⊗ W_F` (source
pair first); let `K` be the unnormalized kept source pair and
`p = F² + (2/3)F(1 − F) + (5/9)(1 − F)²`. Then
1. the probability of keeping the source pair is `tr K = p`;
2. `p > 1/4`;
3. the kept pair has singlet fidelity `⟨Ψ⁻|K/p|Ψ⁻⟩ = F′` with `F′` given by Eq. (7).

**Formalization Note.** The statement is for every `F ∈ [0, 1]` (the paper takes F > 1/2), a
generalization. "F′ > F" is part of `recurrenceMap_iterate`. The final random bilateral
rotation of A3 does not change the singlet fidelity and is not applied. -/
theorem recurrence_step (F : ℝ) (h0 : 0 ≤ F) (h1 : F ≤ 1) :
    (recurrenceKept (Matrix.kronecker (wernerState F) (wernerState F))).trace =
        ((F ^ 2 + (2 / 3) * F * (1 - F) + (5 / 9) * (1 - F) ^ 2 : ℝ) : ℂ) ∧
      1 / 4 < F ^ 2 + (2 / 3) * F * (1 - F) + (5 / 9) * (1 - F) ^ 2 ∧
      singletFidelity
          ((((F ^ 2 + (2 / 3) * F * (1 - F) + (5 / 9) * (1 - F) ^ 2 : ℝ) : ℂ)⁻¹) •
            recurrenceKept (Matrix.kronecker (wernerState F) (wernerState F))) =
        recurrenceMap F := by sorry

end BBPSSW.Distill
