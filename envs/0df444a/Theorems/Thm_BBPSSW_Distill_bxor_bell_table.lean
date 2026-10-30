-- Prove2me | Theorems.Thm_BBPSSW_Distill_bxor_bell_table
-- name    : BBPSSW.Distill.bxor_bell_table
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:46:20.929144+00:00
-- url     : https://prove2.me/theorems/af09dbfa-a739-4fc5-9103-8a9276dcc868
-- title:
--   BXOR acts on pairs of Bell states as in Table (6)
-- statement:
--   For all Bell states $s$ (source pair) and $t$ (target pair),
--
--   $$\mathrm{BXOR}\,(s\otimes t)=c\cdot(s'\otimes t')\qquad\text{for some }|c|=1,$$
--
--   where $(s',t')$ is the entry of Table (6) for $(s,t)$ (`bxorTable`). In particular BXOR leaves $\Phi^+\otimes\Phi^+$ invariant, and a $\Psi^\pm$ source toggles a $\Phi^+$ target to $\Psi^+$ without changing the source: this is the parity check used by the recurrence and breeding protocols.
--
--   Differences from the source:
--   - reading: the result of applying BXOR … omitting phases → equality up to a factor c with |c| = 1; reason: the paper's phase convention
--   - encoding: U_XOR flips the target if the source is up → control on ↑ = 0, index (source, target), source pair first; reason: as Eq. (5) prints it; same instances
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Eq. (5) and Table (6), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_BBPSSW_Distill_bellVec
import Definitions.Def_BBPSSW_Distill_bxor
import Definitions.Def_BBPSSW_Distill_bxorTable

namespace BBPSSW.Distill

/-- **BXOR acts on pairs of Bell states as in Table (6).**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Eq. (5) and Table (6), p. 2: "A BXOR on two Φ+ states leaves them both invariant. The
result of applying BXOR to other combinations of Bell states is shown below, omitting phases."

For all Bell states `s` (source pair) and `t` (target pair),
`BXOR (s ⊗ t) = c · (s' ⊗ t')` with `(s', t') = bxorTable s t`, for some phase `|c| = 1`.

**Formalization Note.** `QAlgorithms.tensorVec u v` is the two-pair vector `(p, q) ↦ u p · v q`,
source pair first, which is the index order of `bxor`. "Omitting phases" is the existential
unit-modulus factor. -/
theorem bxor_bell_table (s t : BellLabel) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      QAlgorithms.act bxor (QAlgorithms.tensorVec (bellVec s) (bellVec t)) =
        c • QAlgorithms.tensorVec (bellVec (bxorTable s t).1) (bellVec (bxorTable s t).2) := by sorry

end BBPSSW.Distill
