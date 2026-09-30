-- Prove2me | Theorems.Thm_Avram2004_Russian_lemma2_i_decreasing
-- name    : Avram2004.Russian.lemma2_i_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:08:21.62164+00:00
-- url     : https://prove2.me/theorems/c6c13db4-ecdf-47cb-9658-56adb6ae1db9
-- title:
--   Lemma 2 (i) — for q > r, f = Z^(q) − qW^(q) decreases monotonically to −∞ on [0, ∞)
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, with Laplace exponent $\psi$, and let $r\ge0$ with $\psi(1)=r$. For $q>r$ define $f:[0,\infty)\to\mathbb R$ by
--   $$f(x)=Z^{(q)}(x)-qW^{(q)}(x).$$
--   Then $f$ is strictly decreasing on $[0,\infty)$ and
--   $$\lim_{x\to\infty}f(x)=-\infty .$$
--
--   Together with Lemma 2 (ii) this shows that the infimum (30) defining the optimal level $\kappa^*$ is either $0$ or the unique positive root of $f$.
--
--   **Formalization Note** The paper says "$f$ decreases monotonically to $-\infty$". Its proof shows $f'<0$ on $(0,\infty)$, and $f(0)=1\ge f(0+)$ because $W^{(q)}(0)=0$ by Definition 2; the reading formalized is strict decrease on $[0,\infty)$. The fact $\Phi(r)=1$ used in the proof follows from $\psi(1)=r$ and is not assumed.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 229, Lemma 2 (i)

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Avram2004.Russian

/-- Lemma 2 (i), p. 229: if `ψ(1) = r ≥ 0` and `q > r`, the function `f(x) = Z^{(q)}(x) - qW^{(q)}(x)` on
`[0, ∞)` decreases (strictly) and tends to `-∞`. -/
theorem lemma2_i_decreasing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevy P X) (hS : Shared.Standing P X)
    (r q : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r) (hq : r < q) :
    StrictAntiOn (fun x => Shared.Z P X 0 q x - q * Shared.W P X 0 q x) (Set.Ici 0) ∧
      Tendsto (fun x => Shared.Z P X 0 q x - q * Shared.W P X 0 q x) atTop atBot := by sorry

end Avram2004.Russian
