-- Prove2me | Theorems.Thm_Avram2004_Russian_lemma2_ii_kappa
-- name    : Avram2004.Russian.lemma2_ii_kappa
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:09:08.027302+00:00
-- url     : https://prove2.me/theorems/dfb1216c-86ba-497b-a76d-26240c12f731
-- title:
--   Lemma 2 (ii) — κ* = 0 if W^(q)(0+) ≥ 1/q; otherwise κ* > 0 is the unique root of Z^(q) = qW^(q)
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumption, with Laplace exponent $\psi$, let $r\ge0$ with $\psi(1)=r$, and let $q>r$. Let $f(x)=Z^{(q)}(x)-qW^{(q)}(x)$ for $x\ge0$ and
--   $$\kappa^*=\inf\{x:\ Z^{(q)}(x)\le qW^{(q)}(x)\}\qquad(30).$$
--   Write $W^{(q)}(0+)=\lim_{x\downarrow0}W^{(q)}(x)$. Then:
--
--   1. if $W^{(q)}(0+)\ge q^{-1}$, then $\kappa^*=0$;
--   2. otherwise $\kappa^*>0$, $f(\kappa^*)=0$, and $\kappa^*$ is the only root of $f$ in $[0,\infty)$.
--
--   This identifies the optimal exercise level of the Russian option: immediate exercise when $W^{(q)}(0+)\ge q^{-1}$ (possible only for bounded variation), and otherwise the root of $Z^{(q)}=qW^{(q)}$.
--
--   **Formalization Note** The paper states the lemma with $\kappa^*$ "as in Theorem 2", i.e. $q=\alpha+r$ with $\alpha>0$; this is the same as $q>r$. The right limit $W^{(q)}(0+)$ is Mathlib's `Function.rightLim`, which is the genuine limit here because $W^{(q)}$ is increasing on $(0,\infty)$ and nonnegative. "The unique root of $f(x)=0$" is read on $f$'s domain $[0,\infty)$; since $f(0)=1$, the root lies in $(0,\infty)$.
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 229, Lemma 2 (ii), with κ* from Eq. (30)

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Russian_russianProblem

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Avram2004.Russian

/-- Lemma 2 (ii), p. 229: if `ψ(1) = r ≥ 0` and `q > r` (i.e. `q = α + r` with `α > 0`), with
`f(x) = Z^{(q)}(x) - qW^{(q)}(x)` and `κ*` as in (30): if `W^{(q)}(0+) ≥ q⁻¹` then `κ* = 0`; otherwise
`κ* > 0` is the unique root of `f(x) = 0` on `[0, ∞)`. -/
theorem lemma2_ii_kappa {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevy P X) (hS : Shared.Standing P X)
    (r q : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r) (hq : r < q) :
    (q⁻¹ ≤ Function.rightLim (Shared.W P X 0 q) 0 → kappaStar P X q = 0) ∧
      (Function.rightLim (Shared.W P X 0 q) 0 < q⁻¹ →
        0 < kappaStar P X q ∧
          Shared.Z P X 0 q (kappaStar P X q) - q * Shared.W P X 0 q (kappaStar P X q) = 0 ∧
          ∀ x : ℝ, 0 ≤ x → Shared.Z P X 0 q x - q * Shared.W P X 0 q x = 0 → x = kappaStar P X q) := by sorry

end Avram2004.Russian
