-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_loglog_absorption
-- name    : ExactDFTRefine.Main.loglog_absorption
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:02:17.791193+00:00
-- url     : https://prove2.me/theorems/64495f93-5306-4c13-8d20-c4c939715a4d
-- title:
--   Proof of Theorem 1.1 — (log log n)^2 = o((log n)^{β−δ}) for the positive constant β − δ
-- statement:
--   With $\beta = 3020165925/10^{12}$ and $\delta = 30201659/10^{10}$, the constant $\beta - \delta$ is positive and
--   $$(\log\log n)^2 = o\big((\log n)^{\beta-\delta}\big) \qquad (n \to \infty,\ n \in \mathbb N).$$
--   Logarithms are natural. This absorbs the $(\log\log n)^2$ overhead of the Fourier reduction into the gap $\beta - \delta$, turning the bound $O(n(\log n)^{1-\beta}(\log\log n)^2)$ into $O(n(\log n)^{1-\delta})$.
--
--   Differences from the source:
--   - encoding: f = o(g) → Asymptotics.IsLittleO atTop on functions ℕ → ℝ; reason: standard little-o along n → ∞
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 6, proof of Theorem 1.1

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

open Asymptotics Filter

namespace ExactDFTRefine.Main

/-- **Proof of Theorem 1.1, absorption of `(log log n)^2`**, p. 6. `β - δ` is positive and
`(log log n)^2 = o((log n)^{β-δ})` as `n → ∞`. -/
theorem loglog_absorption :
    0 < beta - delta ∧
    (fun n : ℕ => Real.log (Real.log (n : ℝ)) ^ 2) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ) ^ (beta - delta)) := by sorry

end ExactDFTRefine.Main
