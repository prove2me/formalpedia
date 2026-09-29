-- Prove2me | Theorems.Thm_DeltaSpikeSupport_aux
-- name    : DeltaSpikeSupport_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:58:46.148393+00:00
-- url     : https://prove2.me/theorems/6e01058e-ff52-4e82-bb2d-b493c1da3b15
-- title:
--   Support of the truncated delta spike lies in $[2^{-\varepsilon}, 2^{\varepsilon}]$
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ have support contained in $[1/2, 2]$ and let $\varepsilon > 0$. Consider the delta spike truncated to the nonnegative axis,
--   $$g(x) \;=\; \begin{cases} 0 & x < 0, \\ \mathrm{DeltaSpike}_{\nu,\varepsilon}(x) & x \ge 0, \end{cases} \qquad \mathrm{DeltaSpike}_{\nu,\varepsilon}(x) = \frac{1}{\varepsilon}\,\nu\!\big(x^{1/\varepsilon}\big).$$
--   Then the support of $g$ is contained in the compact interval
--   $$\operatorname{supp} g \;\subseteq\; \big[2^{-\varepsilon},\, 2^{\varepsilon}\big].$$
--
--   On the negative axis $g$ vanishes by definition, and for $x \ge 0$ nonvanishing of $\nu(x^{1/\varepsilon})$ forces $x^{1/\varepsilon} \in [1/2,2]$, i.e. $x \in [2^{-\varepsilon}, 2^{\varepsilon}]$.
--
--   Stating the support bound for the truncated function is the form needed for Mellin-transform manipulations, where integrands are extended by zero to the whole real line; compact support away from $0$ gives integrability of $g(x)\,x^{s-1}$ for every complex $s$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L461-L473

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

-- TODO: generalize to `RCLike`

local notation (name := mellintransform) "𝓜" => mellin

theorem DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by sorry
