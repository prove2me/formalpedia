-- Prove2me | Theorems.Thm_BetheKS_proposition_4_5
-- name    : BetheKS.proposition_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:36.045254+00:00
-- url     : https://prove2.me/theorems/2927a98f-e584-453c-8747-b125ea626ce8
-- title:
--   Proposition 4.5 — continuity of $\kappa(\delta)$ and the strictly increasing shift $\delta(\mu)$
-- statement:
--   Fix $t\ge\sqrt d>1$ and let $\kappa(\delta)$ be the spectral radius of the transfer operator $\mathcal L=\mathcal L_\delta$ on $L^2(\Omega,\nu)$. Then:
--
--   1. $\kappa(\delta)$ is continuous at every $\delta_0>0$ with $\kappa(\delta_0)>\sqrt d\,c_{\delta_0}$;
--   2. for every $t<\mu\le d$ there is a unique $\delta=\delta(\mu)>0$ with
--   $$
--   \kappa(\delta)=\frac d\mu ;
--   $$
--   3. the function $\mu\mapsto\delta(\mu)$ is strictly increasing on $(t,d]$.
--
--   This defines the limiting outlier locations $-\delta(\mu)$ of Theorem 2.2.
--
--   **Formalization Note** $\kappa$ is valued in $[0,\infty]$; $\delta(\mu)$ is the chosen solution, which is the solution by (2).
--
--   Differences from the source:
--
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: κ(δ) continuous at δ₀ → ContinuousAt of δ ↦ κ(δ) at δ₀ > 0; reason: δ₀ is interior to (0, ∞), so continuity within (0, ∞) and at δ₀ coincide
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Proposition 4.5, p.8 (PDF p.9); proof in App. B.2, pp.16–17

import Mathlib
import Definitions.Def_BetheKS_cavityIter
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

/-- **Proposition 4.5** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.8
(PDF p.9): with `t` fixed, `κ(δ)` is continuous at all `δ₀` with `κ(δ₀) > √d c_{δ₀}`. For every
`t < µ ≤ d` there is a unique `δ = δ(µ) > 0` with `κ(δ) = d/µ`. The function `δ(µ)` is strictly
increasing.

Standing assumptions of §4: `t ≥ √d > 1`; `δ` ranges over `(0, ∞)`.

**Formalization Note.** `κ` takes values in `[0, ∞]` (`spectralRadius`). `δ(µ)` is `deltaOf d t µ`,
the chosen solution; by the uniqueness clause it is the solution. -/
theorem proposition_4_5 (d t : ℝ) (hd : 1 < d) (ht : Real.sqrt d ≤ t) :
    (∀ δ₀ : ℝ, 0 < δ₀ → ENNReal.ofReal (Real.sqrt d * cDelta t δ₀) < kappa d t δ₀ →
      ContinuousAt (fun δ => kappa d t δ) δ₀) ∧
    (∀ μ : ℝ, t < μ → μ ≤ d → ∃! δ : ℝ, 0 < δ ∧ kappa d t δ = ENNReal.ofReal (d / μ)) ∧
    StrictMonoOn (deltaOf d t) (Set.Ioc t d) := by sorry

end BetheKS
