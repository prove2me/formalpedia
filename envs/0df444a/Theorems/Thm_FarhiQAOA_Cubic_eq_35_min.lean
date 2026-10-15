-- Prove2me | Theorems.Thm_FarhiQAOA_Cubic_eq_35_min
-- name    : FarhiQAOA.Cubic.eq_35_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:52.111728+00:00
-- url     : https://prove2.me/theorems/e4f94b43-635d-418f-a8ba-b6bf2fa3a881
-- title:
--   Section V, (35), p. 9 — the scaled p = 1 ratio is at least 0.6924 for all s, t ≥ 0 with 4s + 3t ≤ 1
-- statement:
--   Let $f_{g_4}, f_{g_5}, f_{g_6}$ be the $p=1$ edge functions of the three subgraph types of figure (18). For all real $s, t$ with
--   $$s\ge 0,\qquad t\ge 0,\qquad 4s+3t\le 1,$$
--   there exist angles $\gamma\in[0,2\pi]$ and $\beta\in[0,\pi]$ such that
--   $$s\,f_{g_4}(\gamma,\beta) + (4s+3t)\,f_{g_5}(\gamma,\beta) + \Big(\frac32 - 5s - 3t\Big) f_{g_6}(\gamma,\beta) \;\ge\; 0.6924\,\Big(\frac32 - s - t\Big).$$
--
--   The left side is $F_1/n$ written through (32) with $s = S/n$, $t = T/n$, so its maximum over the angles is $M_1(1,s,t)$. Since $\tfrac32 - s - t > 0$ on the region, the statement says that the ratio (35), $M_1(1,s,t)/(\tfrac32 - s - t)$, is at least $0.6924$ for every admissible $(s,t)$. The paper evaluates (35) numerically and reports its minimum $0.6924$, attained at $s=t=0$.
--
--   **Formalization Note** The constant is exactly $0.6924 = 1731/2500$; the exact minimum $\tfrac12 + \tfrac{1}{3\sqrt3} \approx 0.692450$ is larger by about $5\cdot 10^{-5}$. The angles are restricted to $[0,2\pi]\times[0,\pi]$ as on pp. 2–3. The paper's further claim that the minimum is attained at $s=t=0$ is not part of this statement.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 9, Section V, (35) and the sentence after it

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic

open QAlgorithms

/-- Farhi–Goldstone–Gutmann, Section V, p. 9, (35): for every `s, t ≥ 0` with `4s + 3t ≤ 1` there are
angles `γ ∈ [0, 2π]`, `β ∈ [0, π]` with
`s f_{g₄}(γ, β) + (4s + 3t) f_{g₅}(γ, β) + (3/2 − 5s − 3t) f_{g₆}(γ, β) ≥ 0.6924 (3/2 − s − t)`,
that is, the ratio (35) `M₁(1, s, t)/(3/2 − s − t)` is at least `0.6924` on the whole region. -/
theorem eq_35_min (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : 4 * s + 3 * t ≤ 1) :
    ∃ γ β : ℝ, γ ∈ Set.Icc 0 (2 * Real.pi) ∧ β ∈ Set.Icc 0 Real.pi ∧
      (1731 / 2500 : ℝ) * (3 / 2 - s - t) ≤
        s * fg4 γ β + (4 * s + 3 * t) * fg5 γ β + (3 / 2 - 5 * s - 3 * t) * fg6 γ β := by sorry

end FarhiQAOA.Cubic
