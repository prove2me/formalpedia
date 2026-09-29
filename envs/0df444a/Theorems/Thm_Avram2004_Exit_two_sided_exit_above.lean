-- Prove2me | Theorems.Thm_Avram2004_Exit_two_sided_exit_above
-- name    : Avram2004.Exit.two_sided_exit_above
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:21:53.953917+00:00
-- url     : https://prove2.me/theorems/5b02fb7d-bc83-445c-b1d3-2fe0d5a65098
-- title:
--   Proposition 1, Eq. (9) — upward exit from (a, b): 𝔼_x[e^{−qT_b^+}; T_b^+ < T_a^−] = W^(q)(x−a)/W^(q)(b−a)
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, and write $\mathbb E_x$ for expectation of the process started at $x$ (the path $t\mapsto x+X_t$). Let $T_k^-=\inf\{t>0:X_t\le k\}$ and $T_k^+=\inf\{t>0:X_t\ge k\}$. Let $q\ge0$, $a<b$ and $x\in(a,b)$. Then the random variable $e^{-qT_b^+}\mathbf 1_{\{T_b^+<T_a^-\}}$ is integrable and
--   $$\mathbb E_x\Big[e^{-qT_b^+}\,\mathbf 1_{\{T_b^+<T_a^-\}}\Big]=\frac{W^{(q)}(x-a)}{W^{(q)}(b-a)} .$$
--
--   This is the Laplace transform of the two-sided exit time on the event that $X$ leaves $(a,b)$ above. It is classical (Bertoin, *Lévy Processes*, Theorem VII.8) and is the basic input of the reflected exit problem.
--
--   **Formalization Note** On the event $\{T_b^+<T_a^-\}$ the time $T_b^+$ is finite, so the convention $e^{-q\cdot\infty}=0$ plays no role.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 219, Proposition 1, Eq. (9)

import Mathlib
import Definitions.Def_Avram2004_Exit_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Exit_passageTimes

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Exit

/-- Proposition 1, (9), p. 219: for `q ≥ 0`, `a < b` and `X` started at `x ∈ (a, b)`,
`𝔼_x[e^{-qT_b^+} I(T_b^+ < T_a^-)] = W^{(q)}(x - a) / W^{(q)}(b - a)`. -/
theorem two_sided_exit_above {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (q a b x : ℝ) (hq : 0 ≤ q) (hab : a < b) (hx : x ∈ Set.Ioo a b) :
    Integrable (fun ω => if Tplus x X b ω < Tminus x X a ω then discount q (Tplus x X b ω) else 0) P ∧
    ∫ ω, (if Tplus x X b ω < Tminus x X a ω then discount q (Tplus x X b ω) else 0) ∂P
      = Shared.W P X 0 q (x - a) / Shared.W P X 0 q (b - a) := by sorry

end Avram2004.Exit
