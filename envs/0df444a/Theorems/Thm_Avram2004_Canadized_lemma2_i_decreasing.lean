-- Prove2me | Theorems.Thm_Avram2004_Canadized_lemma2_i_decreasing
-- name    : Avram2004.Canadized.lemma2_i_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T06:39:21.509986+00:00
-- url     : https://prove2.me/theorems/20dee7c6-6680-429b-a728-e780925c6c64
-- title:
--   Lemma 2 (i) — for q > r, Z^(q) − qW^(q) decreases to −∞
-- statement:
--   Let $X$ be a spectrally negative Lévy process under $\mathbb P$ satisfying the paper's standing assumption (unbounded variation, or bounded variation and $\Lambda(dx)\ll dx$). Let $r\ge0$ with $\psi(1)=r$, where $\psi(\theta)=\log\mathbb E[e^{\theta X_1}]$. For $q>r$ define $f:[0,\infty)\to\mathbb R$ by
--   $$
--   f(x)=Z^{(q)}(x)-qW^{(q)}(x),
--   $$
--   where $W^{(q)}$ is the $q$-scale function of $X$ and $Z^{(q)}(x)=1+q\int_{-\infty}^xW^{(q)}(y)\,dy$. Then $f$ is strictly decreasing on $[0,\infty)$ and $f(x)\to-\infty$ as $x\to\infty$.
--
--   In the Canadized Russian problem this is used with $q=p=\alpha+\lambda+r$: it guarantees that the level $\kappa_*=\inf\{x\ge0: f(x)\le-\lambda/(p-\lambda)\}$ is well defined and is the unique crossing point (Lemma 4).
--
--   **Formalization Note** The paper writes "$f$ decreases monotonically to $-\infty$"; we read it as strict decrease on $[0,\infty)$ together with divergence to $-\infty$. The lemma is stated for a generic $q>r$, of which $q=p$ is an instance.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 229, Lemma 2 (i)

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Canadized

/-- Lemma 2 (i), p. 229: if `ψ(1) = r ≥ 0` and `q > r`, the function `f(x) = Z^{(q)}(x) - qW^{(q)}(x)` on
`[0, ∞)` decreases (strictly) and tends to `-∞`. (Used in §7 at `q = p = α + λ + r`.) -/
theorem lemma2_i_decreasing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevy P X) (hS : Shared.Standing P X)
    (r q : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r) (hq : r < q) :
    StrictAntiOn (fun x => Shared.Z P X 0 q x - q * Shared.W P X 0 q x) (Set.Ici 0) ∧
      Tendsto (fun x => Shared.Z P X 0 q x - q * Shared.W P X 0 q x) atTop atBot := by sorry

end Avram2004.Canadized
