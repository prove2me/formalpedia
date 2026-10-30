-- Prove2me | Theorems.Thm_BBPSSW_Distill_bilateral_rotation_bell
-- name    : BBPSSW.Distill.bilateral_rotation_bell
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:46:04.425837+00:00
-- url     : https://prove2.me/theorems/bb424e07-c1e0-41cd-adb8-51bc057ea5ce
-- title:
--   Bilateral $\pi/2$ rotations $B_x,B_y,B_z$ permute the Bell states
-- statement:
--   Let $R_a=\frac{\sqrt2}{2}(1-i\sigma_a)$ be the rotation of one spin by $\pi/2$ about the axis $a$, and $B_a=R_a\otimes R_a$. For every Bell state $b$,
--
--   $$B_a\,b=c\cdot\beta_a(b)\qquad\text{for some }|c|=1,$$
--
--   where $\beta_x$ swaps $\Phi^+\leftrightarrow\Psi^+$, $\beta_y$ swaps $\Phi^-\leftrightarrow\Psi^+$, $\beta_z$ swaps $\Phi^+\leftrightarrow\Phi^-$, and each fixes $\Psi^-$ and the remaining triplet (`bilMap`).
--
--   $B_y$ is used in step B3 of breeding to turn $\Phi^-$ into $\Psi^+$ while leaving $\Phi^+$ invariant.
--
--   Differences from the source:
--   - reading: again we omit phases → equality up to a factor c with |c| = 1; reason: the paper's phase convention
--   - encoding: rotation by π/2 about an axis (sense not fixed) → R_a = (√2/2)(1 − iσ_a) = exp(−iπσ_a/4); reason: the opposite sense gives the same permutation up to phase
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered bullet (bilateral π/2 rotations)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_BBPSSW_Distill_bellVec
import Definitions.Def_BBPSSW_Distill_halfPiRot
import Definitions.Def_BBPSSW_Distill_bilateral
import Definitions.Def_BBPSSW_Distill_bilMap

namespace BBPSSW.Distill

/-- **Bilateral π/2 rotations permute the Bell states.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2 (unnumbered bullet): "Bilateral π/2 rotations Bx, By, and Bz of both particles in a
pair about the x, y, or z axis respectively. Each of these operations leaves the singlet state
and a different one of the triplets invariant, interchanging the other two triplets, with Bx
mapping Φ+ ↔ Ψ+, By mapping Φ− ↔ Ψ+, and Bz mapping Φ+ ↔ Φ−. Again we omit phases."

For each axis `a` and Bell state `b`, `B_a b = c · bilMap a b` for some phase `|c| = 1`, where
`B_a = R_a ⊗ R_a` and `R_a = halfPiRot a` is the π/2 rotation about axis `a`. (`bilMap a` fixes
Ψ⁻ and one triplet and swaps the other two, as listed.)

**Formalization Note.** "Omitting phases" is the existential unit-modulus factor. -/
theorem bilateral_rotation_bell (a : Axis) (b : BellLabel) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      QAlgorithms.act (bilateral (halfPiRot a)) (bellVec b) = c • bellVec (bilMap a b) := by sorry

end BBPSSW.Distill
