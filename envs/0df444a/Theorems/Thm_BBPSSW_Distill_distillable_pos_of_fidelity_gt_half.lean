-- Prove2me | Theorems.Thm_BBPSSW_Distill_distillable_pos_of_fidelity_gt_half
-- name    : BBPSSW.Distill.distillable_pos_of_fidelity_gt_half
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:48:23.522094+00:00
-- url     : https://prove2.me/theorems/9d4f6eaa-e629-43c0-9c2e-05022e2ecfcc
-- title:
--   Every two-qubit state with singlet fidelity $\langle\Psi^-|M|\Psi^-\rangle>1/2$ has positive distillable entanglement
-- statement:
--   Let $M$ be a density matrix of two spin-$\tfrac12$ particles, Alice holding the first and Bob the second, with singlet fidelity
--
--   $$\langle\Psi^-|M|\Psi^-\rangle>\tfrac12 .$$
--
--   Then its distillable entanglement is positive:
--
--   $$D(M)>0 .$$
--
--   That is, from $n$ copies of $M$, local operations and two-way classical communication produce $m_n$ pairs with fidelity to $(\Psi^-)^{\otimes m_n}$ tending to one, at a rate $m_n/n$ tending to a positive limit. This is the paper's headline: $F=\tfrac12$ is the threshold above which noisy singlets can be purified and used for faithful teleportation through a noisy channel.
--
--   Differences from the source:
--   - reading: the yield D(M) of pure singlets distillable from M (defined in words) → D(M) = supremum in [0, ∞] of the rates r with finite-round two-way LOCC protocols, m_n/n → r and fidelity with Ψ−^⊗m_n → 1; reason: standard operational definition; finite-round LOCC is a subclass of LOCC, so the statement is not weaker than under a broader LOCC class
--   - encoding: ⟨Ψ−|M|Ψ−⟩ → the real part of ⟨Ψ−|M|Ψ−⟩; reason: the value is real for a density matrix
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Abstract, p. 1 ("showing D(M) > 0 if ⟨Ψ−|M|Ψ−⟩ > 1/2"), restated p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_singletFidelity
import Definitions.Def_BBPSSW_Distill_distillableEntanglement

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)

namespace BBPSSW.Distill

/-- **Every two-qubit state with singlet fidelity above 1/2 has positive distillable
entanglement.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Abstract, p. 1: "We give upper and lower bounds on the yield D(M) of pure singlets
(|Ψ−⟩) distillable from mixed states M, showing D(M) > 0 if ⟨Ψ−|M|Ψ−⟩ > 1/2." Restated on
p. 4: "F = 1/2 is a threshold … above which they can be used as a starting material to make
pure singlets."

Let `M` be a density matrix of two spin-1/2 particles (Alice holding the first) with
`⟨Ψ⁻|M|Ψ⁻⟩ > 1/2`. Then `D(M) > 0`: some positive rate of near-perfect singlets can be
distilled from copies of `M` by finite-round local operations and two-way classical
communication.

**Formalization Note.** `D(M)` is `distillableEntanglement`: the supremum in `[0, ∞]` of the
rates `r` for which `FiniteLOCC` protocols take `M^{⊗n}` to `m_n` pairs with `m_n / n → r`
and fidelity with `Ψ⁻^{⊗ m_n}` tending to 1. -/
theorem distillable_pos_of_fidelity_gt_half (M : Matrix QQ QQ ℂ)
    (hM : QAlgorithms.IsDensityMatrix M) (hF : 1 / 2 < singletFidelity M) :
    0 < distillableEntanglement M := by sorry

end BBPSSW.Distill
