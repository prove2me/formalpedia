-- Prove2me | Theorems.Thm_FloatPointSynth_Gearbox_eq_A3
-- name    : FloatPointSynth.Gearbox.eq_A3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T04:00:24.376026+00:00
-- url     : https://prove2.me/theorems/907c34a4-d005-41a3-b5d0-7c085bfa0a79
-- title:
--   Eq. (A3) — E(x_d) = 2E(N_d)E(x_{d−1})
-- statement:
--   Let $U$ be a $2\times2$ complex matrix and $q\ge2$. Let $x_q$ be the number of applications of $C^{\circ1}(U)$ before $C^{\circ q}(U)$ succeeds, with the law given by (A1), and $N_q$ the number of level-$q$ trials. Then, with means taken in $[0,\infty]$,
--   $$\mathbb E(x_q)=2\,\mathbb E(N_q)\,\mathbb E(x_{q-1}).$$
--
--   This is Wald's identity for the random sum (A1); unfolded from $\mathbb E(x_1)=\mathbb E(N_1)$ it gives the mean clause of Theorem 2.
--
--   Differences from the source:
--   - generalization: $U\in U(2)$ (Definition 1) → any $2\times2$ complex matrix $U$, means in $[0,\infty]$ (possibly infinite); reason: the identity holds for the compound sum whatever the laws; for unitary $U$ it is the paper's (A3) with finite means.
--   - encoding: $d\ge2$ → $q\ge2$ with $x_{q-1}$ written `xLaw U (q - 1)`; reason: renaming.
-- source:
--   Wiebe and Kliuchnikov, Floating Point Representations in Quantum Circuit Synthesis, arXiv:1305.5528v3, p. 15, Appendix A, Eq. (A3)

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Cost

namespace FloatPointSynth.Gearbox

/-- Eq. (A3), p. 15: `E(x_q) = 2 E(N_q) E(x_{q-1})` for every `q ≥ 2`, with means in `[0, ∞]`. -/
theorem eq_A3 (U : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) (hq : 2 ≤ q) :
    pmfMean (xLaw U q) =
      2 * pmfMean (geomPos (levelProb U q)) * pmfMean (xLaw U (q - 1)) := by sorry

end FloatPointSynth.Gearbox
