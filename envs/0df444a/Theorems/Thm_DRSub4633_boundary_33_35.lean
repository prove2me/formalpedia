-- Prove2me | Theorems.Thm_DRSub4633_boundary_33_35
-- name    : DRSub4633.boundary_33_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:08:49.375352+00:00
-- url     : https://prove2.me/theorems/eb760a1e-605d-46e7-b274-1c497aafe335
-- title:
--   Section 4.2, (33)–(35) — three boundary inequalities
-- statement:
--   Let $f$ be nonnegative, continuously differentiable and DR-submodular on $Q$ and fix $x\in Q$. For every small comparator block $o_S\in[0,1]^S$ and every $t\in[0,1]$, with $E^*=e(o_S)$ and $\eta(t)=e^{-st}$,
--   $$Q_t(o_S)\ge\eta(t)E^*,\tag{33}$$
--   $$Q_t(o_S)\ge bE(t)+\langle\nu_t,\,o_S-u\rangle,\tag{34}$$
--   $$E'(t)+sE(t)\ge 0.\tag{35}$$
--   These control the boundary value $E$ along the small path.
--
--   Differences from the source:
--   - encoding: objective defined on Q only; R^n with coordinatewise order; C^1 with boundary derivatives the continuous extensions of interior ones → f a total function on EuclideanSpace ℝ (Fin n), hypotheses on the cube only, values off the cube never read; the order written coordinatewise; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, fderivWithin the cube); reason: Lean convention; on the cube the within-cube derivative of a C^1 function is the continuous extension of the interior derivative, so the instances are the same
--   - encoding: block vectors o_S, o_L, r, l indexed by S and L → functions on Fin n of which only the relevant block is read (mergePt); reason: Lean convention; same instances
--   - encoding: E'(t) → derivWithin E (Set.Icc 0 1) t; reason: Lean convention; E is C^1 on [0,1], so the one-sided derivatives at the endpoints are the page's derivative
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.2, (33)–(35), p.17

import Mathlib
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_DRSub4633_QFace
import Definitions.Def_DRSub4633_nuInc
import Definitions.Def_DRSub4633_Ypath

namespace DRSub4633

/-- **The three boundary inequalities (33)–(35).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.2, (33)–(35), p.17: "For
the small-coordinate comparisons, fix `o = (o_S, o_L)` and write `õ_S = a(t) + (1 − a(t))o_S`,
`E* = e(o_S)`, `η(t) = e^(−st)`. The three boundary inequalities are `Q_t(o_S) ≥ η(t)E*`, (33)
`Q_t(o_S) ≥ bE(t) + ⟨ν_t, o_S − u⟩`, (34) `E′(t) + sE(t) ≥ 0`. (35)"

Standing hypotheses (Sections 3.1 and 4.1, pp.7–10): `f` nonnegative, `C¹` and DR-submodular on
`Q = [0, 1]^n`; `x ∈ Q` is the fixed state.

**Formalization Note.** `E(t) = Y₀(t) = F(a(t), 1_L)`. `o_S` is a function on `Fin n`; only its
small coordinates are read. `E′(t)` is the derivative of `E` within `[0, 1]` at `t`. The claim is
for every `o_S ∈ [0, 1]^S` and `t ∈ [0, 1]`, including `S = ∅`. -/
theorem boundary_33_35 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : ∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) (hf : GeomDRSub.IsDRSubmodular f)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ GeomDRSub.cube n)
    (oS : Fin n → ℝ) (hoS : ∀ j, x j ≤ sPar → 0 ≤ oS j ∧ oS j ≤ 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (-(sPar * t)) * eFace f x oS ≤ QFace f x t oS ∧
    bPar * Ypath f x 0 t + ∑ j ∈ Finset.univ.filter (fun j : Fin n => x j ≤ sPar),
        nuInc f x t j * (oS j - x j) ≤ QFace f x t oS ∧
    0 ≤ derivWithin (fun r => Ypath f x 0 r) (Set.Icc (0 : ℝ) 1) t + sPar * Ypath f x 0 t := by sorry

end DRSub4633
