-- Prove2me | Theorems.Thm_BetheKS_observation_4_2
-- name    : BetheKS.observation_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:41.925821+00:00
-- url     : https://prove2.me/theorems/d790bdf0-6c67-47bc-949b-97d7658beee0
-- title:
--   Observation 4.2 — the transfer operator is well-defined: $\|\mathcal L\|<\infty$
-- statement:
--   Fix $t\ge\sqrt d>1$ and $\delta>0$. The map
--   $$
--   (\mathcal Lf)(T):=\Gamma(T)\sum_{j=1}^Kf(T_j)
--   $$
--   of Definition 4.1 is well-defined on $L^2(\Omega,\nu)$; in other words, $\|\mathcal L\|<\infty$.
--
--   **Formalization Note** Stated as the existence of a bounded linear operator on $L^2(\Omega,\nu;\mathbb C)$ whose value on every $f$ agrees $\nu$-a.e. with the formula.
--
--   Differences from the source:
--
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Observation 4.2, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_BetheKS_GWTree

set_option autoImplicit false

open MeasureTheory

namespace BetheKS

/-- **Observation 4.2** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.7
(PDF p.8): the map `(ℒ f)(T) := Γ(T) ∑_{j=1}^{K} f(T_j)` of Definition 4.1 is well-defined on
`L²(Ω, ν)`; in other words, `‖ℒ‖ < ∞`.

Standing assumptions of §4 (p.7): `t ≥ √d > 1`, `δ > 0`; `ν` is the `Poi(d)` Galton–Watson law.

**Formalization Note.** Stated as the existence of a bounded linear operator on `L²(Ω, ν; ℂ)` whose
value on every `f` agrees `ν`-a.e. with the formula (on any representative of `f`). -/
theorem observation_4_2 (d t δ : ℝ) (hd : 1 < d) (ht : Real.sqrt d ≤ t) (hδ : 0 < δ) :
    ∃ T : Lp ℂ 2 (gwLaw d) →L[ℂ] Lp ℂ 2 (gwLaw d), ∀ f : Lp ℂ 2 (gwLaw d),
      (T f : Offspring → ℂ) =ᵐ[gwLaw d]
        (fun K => (treeGamma t δ K : ℂ) * ∑ j ∈ Finset.range (K []), (f : Offspring → ℂ) (subtree K j)) := by sorry

end BetheKS
