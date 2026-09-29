-- Prove2me | Theorems.Thm_FamousTheorems_gagliardo_nirenberg_sobolev
-- name    : FamousTheorems.gagliardo_nirenberg_sobolev
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:46.303531+00:00
-- url     : https://prove2.me/theorems/3b64e44f-a513-4563-99f3-383574c2e4bf
-- title:
--   The Gagliardo–Nirenberg–Sobolev inequality
-- statement:
--   **The Gagliardo–Nirenberg–Sobolev inequality.** Let $E$ be a real normed space of dimension $n\ge1$ with an additive Haar measure $\mu$, and $F$ a finite-dimensional real normed space. Let $1\le p$ and $p'$ satisfy $\tfrac1{p'}=\tfrac1p-\tfrac1n$. Then there is a constant $C$ such that every compactly supported $C^1$ function $u:E\to F$ satisfies
--   $$\|u\|_{L^{p'}(\mu)}\le C\,\|Du\|_{L^p(\mu)}.$$
--
--   This is the Sobolev embedding $W^{1,p}\hookrightarrow L^{p^*}$ for $p<n$, with $p^*=np/(n-p)$ the Sobolev conjugate. It is fundamental in the theory of partial differential equations and the calculus of variations. It is used to prove existence and regularity of weak solutions and in the study of critical exponents.
--
--   **Formalization note.** Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, with Mathlib's explicit constant `SNormLESNormFDerivOfEqConst F μ p` supplying the witness. The exponents are nonnegative reals (`NNReal`). The relation between them is stated in `ℝ`, and $1\le p$ together with $0<n$ forces $p<n$ when $p'$ is finite. `eLpNorm` is the extended $L^p$ seminorm and `fderiv ℝ u` is the Fréchet derivative.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem gagliardo_nirenberg_sobolev {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {p p' : NNReal} (hp : 1 ≤ p) (hn : 0 < Module.finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (Module.finrank ℝ E : ℝ)⁻¹) :
    ∃ C : NNReal, ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u p' μ ≤ C * eLpNorm (fderiv ℝ u) p μ := by sorry

end FamousTheorems
