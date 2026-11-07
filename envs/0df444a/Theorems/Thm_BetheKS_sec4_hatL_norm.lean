-- Prove2me | Theorems.Thm_BetheKS_sec4_hatL_norm
-- name    : BetheKS.sec4_hatL_norm
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:11.337427+00:00
-- url     : https://prove2.me/theorems/f701aafe-8c63-4c28-914d-9d441d780086
-- title:
--   §4 (norm of $\widehat{\mathcal L}$), p.8 — $\|\widehat{\mathcal L}\|\le\sqrt d\,c_\delta<1$
-- statement:
--   Fix $t\ge\sqrt d>1$ and $\delta>0$. With $\Pi f:=(\mathbb E_\nu f)\mathbf 1$ and $\widehat{\mathcal L}:=\mathcal L(I-\Pi)$,
--   $$
--   \|\widehat{\mathcal L}\|\le\sqrt d\,c_\delta,\qquad\sqrt d\,c_\delta=\frac{\sqrt d\,t}{t^2+\delta}<1 .
--   $$
--   This is the bound behind the spectral gap of $\mathcal L$ (Proposition 4.4): $\mathcal L$ is a rank-one perturbation of an operator of norm less than one.
--
--   Differences from the source:
--
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - encoding: ‖ℒ̂‖ ≤ √d c_δ → ‖ℒ(f − (E f)1)‖₂ ≤ √d c_δ ‖f‖₂ for every f ∈ L²(Ω, ν; ℂ); reason: the definition of the operator norm
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), §4, p.8 (PDF p.9), display "Hence ‖ℒ̂‖ ≤ √d c_δ"

import Mathlib
import Definitions.Def_BetheKS_cavityIter
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory

namespace BetheKS

/-- **§4 (norm of `ℒ̂`)** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.8
(PDF p.9): with `Π f := (E_ν f) 1` and `ℒ̂ := ℒ(I − Π)`, "Hence `‖ℒ̂‖ ≤ √d c_δ`. Note that
`√d c_δ = √d t/(t² + δ) < 1`."

Standing assumptions of §4: `t ≥ √d > 1`, `δ > 0`.

**Formalization Note.** `‖ℒ̂‖ ≤ √d c_δ` is stated as `‖ℒ(f − (E f)1)‖₂ ≤ √d c_δ ‖f‖₂` for every
`f ∈ L²(Ω, ν; ℂ)`, which is the operator-norm bound. -/
theorem sec4_hatL_norm (d t δ : ℝ) (hd : 1 < d) (ht : Real.sqrt d ≤ t) (hδ : 0 < δ) :
    (∀ f : Lp ℂ 2 (gwLaw d),
      ‖transferOp d t δ (f - Lp.const 2 (gwLaw d) (∫ K, (f : Offspring → ℂ) K ∂gwLaw d))‖ ≤
        Real.sqrt d * cDelta t δ * ‖f‖) ∧
    Real.sqrt d * cDelta t δ < 1 := by sorry

end BetheKS
