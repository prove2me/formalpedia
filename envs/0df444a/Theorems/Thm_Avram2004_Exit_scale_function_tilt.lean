-- Prove2me | Theorems.Thm_Avram2004_Exit_scale_function_tilt
-- name    : Avram2004.Exit.scale_function_tilt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:21:27.250388+00:00
-- url     : https://prove2.me/theorems/351a1dbe-438c-445c-90a4-44049440526b
-- title:
--   Remark 4 — W^(u)(x) = e^{vx} W_v^(u−ψ(v))(x)
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, with Laplace exponent $\psi$. Let $v$ be such that $\psi(v)<\infty$. Then for every real $u$ and every real $x$,
--   $$W^{(u)}(x)=e^{vx}\,W_v^{(u-\psi(v))}(x),$$
--   where $W^{(u)}$ is the $u$-scale function of $\psi$ and $W_v^{(p)}$ the $p$-scale function of the tilted exponent $\psi_v(\theta)=\psi(\theta+v)-\psi(v)$ (both given by Definition 2 for nonnegative index and by the series (5) for negative index).
--
--   The paper states the identity for $u\ge\psi(v)$ and then, "by analytical extension", for all $u\in\mathbb C$. It converts every scale function of the Esscher-transformed process into one of the original process, and is used in (16), in (22) and in the analytic-continuation step of Theorem 1.
--
--   **Formalization Note** "$\psi(v)<\infty$" is integrability of $e^{vX_1}$. The statement covers every real $u$ (including $u<0$ and $0\le u<\psi(v)$, where one or both sides are given by the series (5)); complex $u$ are not formalized, since no statement of the paper evaluates a scale function at a non-real index.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 218, Remark 4

import Mathlib
import Definitions.Def_Avram2004_Exit_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Exit

/-- Remark 4, p. 218: for `v` with `ψ(v) < ∞` (i.e. `e^{vX_1}` integrable) and every real `u`,
`W^{(u)}(x) = e^{vx} W_v^{(u - ψ(v))}(x)` for all `x`. -/
theorem scale_function_tilt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (v : ℝ) (hv : Integrable (fun ω => Real.exp (v * X 1 ω)) P) (u x : ℝ) :
    Shared.W P X 0 u x = Real.exp (v * x) * Shared.W P X v (u - Shared.psi P X v) x := by sorry

end Avram2004.Exit
