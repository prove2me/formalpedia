-- Prove2me | Theorems.Thm_BBPSSW_Distill_singlet_bilateral_invariant
-- name    : BBPSSW.Distill.singlet_bilateral_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:45:57.170867+00:00
-- url     : https://prove2.me/theorems/a4c4f177-b507-4841-8d5e-e21b0c4d7cb4
-- title:
--   The singlet is invariant under bilateral rotations: $(U\otimes U)\Psi^-=\det U\,\Psi^-$
-- statement:
--   For every $2\times2$ complex matrix $U$,
--
--   $$(U\otimes U)\,\Psi^-=\det U\cdot\Psi^- .$$
--
--   In particular, for $U\in SU(2)$ the singlet is invariant: $(U\otimes U)\Psi^-=\Psi^-$. This is why a random bilateral rotation does not change the singlet fidelity $F$ of a state.
--
--   Differences from the source:
--   - generalization: invariance of Ψ− under bilateral SU(2) rotations → (U ⊗ U)Ψ− = det U · Ψ− for every 2 × 2 complex matrix U; reason: det U = 1 on SU(2), so it specializes to the source
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered ("Because of the singlet's invariance under bilateral rotations")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_BBPSSW_Distill_bellVec
import Definitions.Def_BBPSSW_Distill_bilateral

namespace BBPSSW.Distill

/-- **The singlet is invariant under bilateral rotations.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2 (unnumbered): "Because of the singlet's invariance under bilateral rotations, the
symmetrized state WF, which we shall call a Werner state [7] of purity F, has the same F as the
initial mixed state M from which it was derived."

For every 2 × 2 complex matrix `U`, `(U ⊗ U) Ψ⁻ = det U · Ψ⁻`; for `U ∈ SU(2)` this is
`(U ⊗ U) Ψ⁻ = Ψ⁻`.

**Formalization Note.** `QAlgorithms.act A ψ` is the matrix–vector product `A ψ`. The
statement covers every matrix `U` (the factor `det U` is `1` on SU(2)), a generalization. -/
theorem singlet_bilateral_invariant (U : Matrix (Fin 2) (Fin 2) ℂ) :
    QAlgorithms.act (bilateral U) (bellVec .psiMinus) = U.det • bellVec .psiMinus := by sorry

end BBPSSW.Distill
