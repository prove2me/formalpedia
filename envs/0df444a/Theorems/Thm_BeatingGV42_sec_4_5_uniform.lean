-- Prove2me | Theorems.Thm_BeatingGV42_sec_4_5_uniform
-- name    : BeatingGV42.sec_4_5_uniform
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:49.38518+00:00
-- url     : https://prove2.me/theorems/c43ccae1-b3bf-47cb-b79d-ce60c4213028
-- title:
--   §4.5 uniformity — one $t_0<1/49$ and one $\varepsilon>0$ with $\Psi_{a_{GV}(\delta)+\varepsilon,42}(t_0,\delta)<0$ for all $\delta\in I$
-- statement:
--   With $I=[0.39,0.48]$ there is a single $t_0$ with $0<t_0<1/49$ such that
--   $$
--   \Psi_{a_{GV}(\delta),42}(t_0,\delta)<0\quad\text{for every }\delta\in I,
--   $$
--   and there is then a constant $\varepsilon>0$ such that for every $\delta\in I$ the choice $a(\delta)=a_{GV}(\delta)+\varepsilon$ still satisfies $a(\delta)<1$ and $\Psi_{a(\delta),42}(t_0,\delta)<0$.
--
--   Feeding $a(\delta)$, $t_0$ into Proposition 4.9 gives rate $R(a(\delta))=1-H_{42}(\delta)+\varepsilon\ln49/\ln42$, which proves Theorem 1.1 with $\beta=\varepsilon\ln49/\ln42$, independent of $\delta$.
--
--   **Formalization Note** $\Psi$ is `Psi 49 42`. The same $t_0$ and $\varepsilon$ serve all $\delta\in I$.
--
--   Differences from the source:
--   - reading: a single t_0 < 1/49 → 0 < t₀ ∧ t₀ < 1/49; reason: footnote 2 takes t_0 = b − η with b = 1/49 and 0 < η < b/2, so t_0 > 0; Proposition 4.9 needs t ∈ (0, 1/Q)
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §4.5, pp.24–25 (PDF pp.26–27), with footnote 2

import Mathlib
import Definitions.Def_BeatingGV42_Psi
import Definitions.Def_BeatingGV42_aGV

set_option autoImplicit false

namespace BeatingGV42

/-- **Uniformity in `δ`** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.5, pp.24–25 (PDF pp.26–27), with footnote 2): "a single t_0 < 1/49,
sufficiently close to 1/49, satisfies Ψ_{a_GV(δ),42}(t_0, δ) < 0 for every δ ∈ I. By continuity and
compactness, there is then a constant ε > 0 such that, for every δ ∈ I, the choice
a(δ) := a_GV(δ) + ε still satisfies a(δ) < 1 and Ψ_{a(δ),42}(t_0, δ) < 0."

**Formalization Note** `I = [0.39, 0.48]`. `t_0 > 0` is stated: footnote 2 constructs
`t_0 = b − η` with `b = 1/49` and `0 < η < b/2`, and Proposition 4.9 needs `t ∈ (0, 1/Q)`. One `t_0` and one
`ε` serve every `δ ∈ I`. -/
theorem sec_4_5_uniform :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < 1 / 49 ∧
      (∀ δ ∈ Set.Icc (39 / 100 : ℝ) (48 / 100), Psi 49 42 (aGV δ) t₀ δ < 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ ∈ Set.Icc (39 / 100 : ℝ) (48 / 100),
        aGV δ + ε < 1 ∧ Psi 49 42 (aGV δ + ε) t₀ δ < 0 := by sorry

end BeatingGV42
