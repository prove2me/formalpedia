-- Prove2me | Theorems.Thm_Avram2004_Russian_remark3_scale_at_zero
-- name    : Avram2004.Russian.remark3_scale_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:06:59.257723+00:00
-- url     : https://prove2.me/theorems/a172246b-0aee-4891-8072-e96f642a2eaf
-- title:
--   Remark 3 — W_v(0+) = 0 if and only if X has unbounded variation
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, and let $v$ be such that $\psi(v)<\infty$. Then
--   $$\lim_{x\downarrow0}W_v(x)=0\iff X\text{ has unbounded variation},$$
--   where $W_v=W_v^{(0)}$ is the $0$-scale function of the tilted exponent $\psi_v$. Moreover, if $X$ has unbounded variation then $\lim_{x\downarrow0}W_v^{(q)}(x)=0$ for every real $q$.
--
--   The value $W^{(q)}(0+)$ decides which of the three cases of the proof of Theorem 2 occurs: $W^{(q)}(0+)=0$ (unbounded variation), $W^{(q)}(0+)\in(0,q^{-1})$ and $W^{(q)}(0+)\ge q^{-1}$.
--
--   **Formalization Note** "$\psi(v)<\infty$" is integrability of $e^{vX_1}$. "Unbounded variation" is read as the negation of "almost every path has bounded variation on every compact interval"; for a Lévy process these are the only two alternatives. The paper cites the equivalence from Bertoin (Corollary VII.1.5) and derives the second statement from the expansion (5); it states it for $q$ in the domain of (5), of which the real $q$ are formalized.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 218, Remark 3

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Avram2004.Russian

/-- Remark 3, p. 218: for `v` with `ψ(v) < ∞`, `lim_{x↓0} W_v(x) = 0` if and only if `X` has unbounded
variation; and under the same condition `lim_{x↓0} W_v^{(q)}(x) = 0` for every real `q`. -/
theorem remark3_scale_at_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevy P X) (hS : Shared.Standing P X)
    (v : ℝ) (hv : Integrable (fun ω => Real.exp (v * X 1 ω)) P) :
    (Tendsto (Shared.W P X v 0) (𝓝[>] 0) (𝓝 0) ↔ ¬ Shared.BoundedVar P X) ∧
      (¬ Shared.BoundedVar P X → ∀ q : ℝ, Tendsto (Shared.W P X v q) (𝓝[>] 0) (𝓝 0)) := by sorry

end Avram2004.Russian
