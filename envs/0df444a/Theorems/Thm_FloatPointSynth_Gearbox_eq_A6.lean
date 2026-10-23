-- Prove2me | Theorems.Thm_FloatPointSynth_Gearbox_eq_A6
-- name    : FloatPointSynth.Gearbox.eq_A6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T04:00:30.073863+00:00
-- url     : https://prove2.me/theorems/645799b1-74be-4943-821d-df6e3e7251cb
-- title:
--   Eq. (A6) — V(x_d) = 2V(x_{d−1})E(N_d) + 4V(N_d)(E(x_{d−1}))²
-- statement:
--   Let $U$ be a single-qubit unitary and $q\ge2$, with $x_q$ and $N_q$ as in Appendix A (the law of $x_q$ given by (A1)). Then
--   $$\mathbb V(x_q)=2\,\mathbb V(x_{q-1})\,\mathbb E(N_q)+4\,\mathbb V(N_q)\,\big(\mathbb E(x_{q-1})\big)^2 .$$
--
--   This is the variance identity for the random sum (A1); combined with (A4) and the moments of $N_q$ it gives the recursion (A7) behind the variance bound of Theorem 2.
--
--   **Formalization Note** All moments are in $[0,\infty]$; for unitary $U$ every moment involved is finite, so the identity is the paper's real identity.
--
--   Differences from the source:
--   - encoding: real moments → `ℝ≥0∞`-valued moments; reason: they are finite for unitary $U$, so nothing changes.
--   - encoding: $d\ge2$ → $q\ge2$ with $x_{q-1}$ written `xLaw U (q - 1)`; reason: renaming.
-- source:
--   Wiebe and Kliuchnikov, Floating Point Representations in Quantum Circuit Synthesis, arXiv:1305.5528v3, p. 15, Appendix A, Eq. (A6)

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Cost

namespace FloatPointSynth.Gearbox

/-- Eq. (A6), p. 15: for unitary `U` and every `q ≥ 2`,
`V(x_q) = 2 V(x_{q-1}) E(N_q) + 4 V(N_q) (E(x_{q-1}))²`, in `[0, ∞]`. -/
theorem eq_A6 (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (q : ℕ) (hq : 2 ≤ q) :
    pmfVar (xLaw U q) =
      2 * pmfVar (xLaw U (q - 1)) * pmfMean (geomPos (levelProb U q)) +
        4 * pmfVar (geomPos (levelProb U q)) * pmfMean (xLaw U (q - 1)) ^ 2 := by sorry

end FloatPointSynth.Gearbox
