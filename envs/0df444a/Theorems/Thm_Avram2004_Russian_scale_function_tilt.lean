-- Prove2me | Theorems.Thm_Avram2004_Russian_scale_function_tilt
-- name    : Avram2004.Russian.scale_function_tilt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:05:43.215007+00:00
-- url     : https://prove2.me/theorems/c96d0fff-56eb-4107-96bf-7e62f4320ac4
-- title:
--   Remark 4 — W^(u)(x) = e^{vx} W_v^(u−ψ(v))(x)
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, with Laplace exponent $\psi$. Let $v$ be such that $\psi(v)<\infty$. Then for every real $u$ and every real $x$,
--   $$W^{(u)}(x)=e^{vx}\,W_v^{(u-\psi(v))}(x),$$
--   where $W^{(u)}$ is the $u$-scale function of $\psi$ and $W_v^{(p)}$ the $p$-scale function of the tilted exponent $\psi_v(\theta)=\psi(\theta+v)-\psi(v)$ (both given by Definition 2 for nonnegative index and by the series (5) for negative index).
--
--   The paper states the identity for $u\ge\psi(v)$ and then, "by analytical extension", for all $u\in\mathbb C$. It converts every scale function of the Esscher-transformed process into one of the original process. In the Russian problem it turns the scale functions of $(X,\mathbb P^1)$ in Corollary 1 into those of $(X,\mathbb P)$, and it gives $W^{(q)}(x)=e^{\Phi(q)x}W_{\Phi(q)}(x)$, used in the proof of Lemma 2.
--
--   **Formalization Note** "$\psi(v)<\infty$" is integrability of $e^{vX_1}$. The statement covers every real $u$ (including $u<0$ and $0\le u<\psi(v)$, where one or both sides are given by the series (5)); complex $u$ are not formalized, since no statement of the paper evaluates a scale function at a non-real index.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 218, Remark 4

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Avram2004.Russian

/-- Remark 4, p. 218: for `v` with `ψ(v) < ∞` (i.e. `e^{vX_1}` integrable) and every real `u`,
`W^{(u)}(x) = e^{vx} W_v^{(u - ψ(v))}(x)` for all `x` (the page states it for `u ≥ ψ(v)` and extends
it analytically to all `u ∈ ℂ`; the real case is stated here). -/
theorem scale_function_tilt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevy P X) (hS : Shared.Standing P X)
    (v : ℝ) (hv : Integrable (fun ω => Real.exp (v * X 1 ω)) P) (u x : ℝ) :
    Shared.W P X 0 u x = Real.exp (v * x) * Shared.W P X v (u - Shared.psi P X v) x := by sorry

end Avram2004.Russian
