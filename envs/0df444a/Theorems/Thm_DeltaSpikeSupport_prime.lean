-- Prove2me | Theorems.Thm_DeltaSpikeSupport_prime
-- name    : DeltaSpikeSupport_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:37:57.494172+00:00
-- url     : https://prove2.me/theorems/cdc38686-332a-40ba-ac94-44682c12d12e
-- title:
--   Support of the delta spike is contained in $[2^{-\varepsilon}, 2^{\varepsilon}]$ (contrapositive form)
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ have support contained in $[1/2, 2]$, let $\varepsilon > 0$, and let $x \ge 0$. If the delta spike does not vanish at $x$, then $x$ must lie in the $\varepsilon$-window around $1$:
--   $$\mathrm{DeltaSpike}_{\nu,\varepsilon}(x) \neq 0 \;\Longrightarrow\; x \in \big[2^{-\varepsilon},\, 2^{\varepsilon}\big],$$
--   where $\mathrm{DeltaSpike}_{\nu,\varepsilon}(x) = \nu(x^{1/\varepsilon})/\varepsilon$.
--
--   This is the contrapositive packaging of the support bound: nonvanishing of $\nu(x^{1/\varepsilon})$ forces $x^{1/\varepsilon} \in [1/2,2]$, i.e. $x \in [2^{-\varepsilon}, 2^{\varepsilon}]$.
--
--   Having the implication in this direction is convenient in measure-theoretic arguments (e.g. bounding integrals by restricting to the support), and it feeds directly into the estimates comparing the smoothed and unsmoothed Chebyshev functions in the PNT+ pipeline.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L475-L482

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

theorem DeltaSpikeSupport_prime {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by sorry
