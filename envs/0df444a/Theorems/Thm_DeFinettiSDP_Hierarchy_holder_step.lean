-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_holder_step
-- name    : DeFinettiSDP.Hierarchy.holder_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:42.926641+00:00
-- url     : https://prove2.me/theorems/593a54ab-a461-47ec-bd59-120c769158de
-- title:
--   Proof of Theorem 3.1, p. 11 — Hölder step Tr[G W] ≤ Tr[G V] + ‖G‖∞·‖W − V‖₁
-- statement:
--   For square complex matrices $G$, $W$, $V$ of the same finite size,
--
--   $$\mathrm{Re}\,\mathrm{Tr}[G\,W]\ \le\ \mathrm{Re}\,\mathrm{Tr}[G\,V]+\|G\|_\infty\,\|W-V\|_1,$$
--
--   where $\|G\|_\infty$ is the largest singular value of $G$ and $\|\cdot\|_1$ the trace norm. This is Hölder's inequality $|\mathrm{Tr}[G(W-V)]|\le\|G\|_\infty\|W-V\|_1$ written as it is used in the proof of Theorem 3.1, with $W=W_{AB_1}$ and $V$ the de Finetti approximant.
--
--   **Formalization Note** The paper writes $\mathrm{Tr}[\cdot]$ for the objective; here its real part is used, consistent with the definition of $Q$ and $\mathrm{SDP}_n$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, proof of Theorem 3.1, p. 11, first two lines of the display and "where we used Hölder's inequality"

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems
open Matrix

namespace DeFinettiSDP.Hierarchy

/-- **Hölder step** (arXiv:1810.12197v3, proof of Theorem 3.1, p. 11). For square complex matrices
`G`, `W`, `V` on a finite index set,
`Re Tr[G W] ≤ Re Tr[G V] + ‖G‖_∞ ‖W − V‖₁`. -/
theorem holder_step {ι : Type} [Fintype ι] [DecidableEq ι] (G W V : Matrix ι ι ℂ) :
    (Matrix.trace (G * W)).re ≤
      (Matrix.trace (G * V)).re + opNormInf G * WildeQIT.traceNorm (W - V) := by sorry

end DeFinettiSDP.Hierarchy
