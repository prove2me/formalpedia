-- Prove2me | Theorems.Thm_Avram2004_Exit_two_sided_exit_below
-- name    : Avram2004.Exit.two_sided_exit_below
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:22:32.824958+00:00
-- url     : https://prove2.me/theorems/d2a199aa-a1f3-4e40-8fef-b967396abb16
-- title:
--   Proposition 1, Eq. (10) — downward exit from (a, b) in terms of Z^(q) and W^(q)
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, $\mathbb E_x$ expectation for the process started at $x$, and $T_k^\pm$ the first passage times of Definition 4. Let $q\ge0$, $a<b$ and $x\in(a,b)$. Then $e^{-qT_a^-}\mathbf 1_{\{T_b^+>T_a^-\}}$ is integrable and
--   $$\mathbb E_x\Big[e^{-qT_a^-}\,\mathbf 1_{\{T_b^+>T_a^-\}}\Big]=Z^{(q)}(x-a)-W^{(q)}(x-a)\,\frac{Z^{(q)}(b-a)}{W^{(q)}(b-a)} .$$
--
--   This is the Laplace transform of the two-sided exit time on the event that $X$ leaves $(a,b)$ below (possibly by a jump). Together with (9) it is the complete solution of the two-sided exit problem; the paper takes it from Bertoin (1997), correcting a typographical error there.
--
--   **Formalization Note** On $\{T_b^+>T_a^-\}$ the time $T_a^-$ is finite, so the convention $e^{-q\cdot\infty}=0$ plays no role.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 219, Proposition 1, Eq. (10)

import Mathlib
import Definitions.Def_Avram2004_Exit_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Exit_passageTimes

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Exit

/-- Proposition 1, (10), p. 219: for `q ≥ 0`, `a < b` and `X` started at `x ∈ (a, b)`,
`𝔼_x[e^{-qT_a^-} I(T_b^+ > T_a^-)] = Z^{(q)}(x - a) - W^{(q)}(x - a) Z^{(q)}(b - a) / W^{(q)}(b - a)`. -/
theorem two_sided_exit_below {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (q a b x : ℝ) (hq : 0 ≤ q) (hab : a < b) (hx : x ∈ Set.Ioo a b) :
    Integrable (fun ω => if Tminus x X a ω < Tplus x X b ω then discount q (Tminus x X a ω) else 0) P ∧
    ∫ ω, (if Tminus x X a ω < Tplus x X b ω then discount q (Tminus x X a ω) else 0) ∂P
      = Shared.Z P X 0 q (x - a) - Shared.W P X 0 q (x - a) * Shared.Z P X 0 q (b - a) / Shared.W P X 0 q (b - a) := by sorry

end Avram2004.Exit
