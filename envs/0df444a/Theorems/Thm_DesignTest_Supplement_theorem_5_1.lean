-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_1
-- name    : DesignTest.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:10:53.973719+00:00
-- url     : https://prove2.me/theorems/2dec9ccd-9dfd-4c25-bcbf-cc89ecd6ae58
-- title:
--   Theorem 5.1 — Impossibility of Haar unitary testing in TV distance
-- statement:
--   Let $d\ge2$, $\varepsilon_{\mathrm{far}}\in(0,1)$, $\delta_{\mathrm{fail}}\in[0,1/2)$, and let $H$ be the Haar measure on $U(d)$. For every integer $m\ge0$ there is **no** test that receives the full matrices of $m$ independent samples from an unknown probability measure $\nu$ on $U(d)$ and satisfies both
--
--   $$\Pr[\text{accept}\mid\nu=H]\ge1-\delta_{\mathrm{fail}},\qquad \Pr[\text{accept}\mid\nu]\le\delta_{\mathrm{fail}}\ \text{ whenever }\ \mathrm{Dist}_{\mathrm{TV}}(H,\nu)>\varepsilon_{\mathrm{far}} .$$
--
--   This rules out a uniform Haar test for unitaries in TV distance and motivates unitary design testing.
--
--   **Formalization Note.** A test is a measurable acceptance function $f:U(d)^m\to[0,1]$.
--
--   Differences from the source:
--   - encoding: classical-description algorithm making at most m sample requests, with arbitrary processing and internal randomness → measurable f : X^m → [0, 1] (acceptance probability); reason: samples may be drawn in advance (§3.2, p.14); averaging internal randomness and measurements gives f
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.1, p.44 (PDF p.47)

import Mathlib
import Definitions.Def_DesignTest_Supplement_tvDist
import Definitions.Def_DesignTest_Supplement_twirlDist

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.1** (Impossibility of Haar unitary testing in TV distance). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.1, p.44.

Fix `d ≥ 2`, `ε_far ∈ (0, 1)` and `δ_fail ∈ [0, 1/2)`. For every `m ≥ 0` there is no test given the
complete classical descriptions (full matrices) of `m` independent samples from a probability measure
`ν` on `U(d)` that accepts `ν = H` with probability at least `1 − δ_fail` and accepts every `ν` with
`Dist_TV(H, ν) > ε_far` with probability at most `δ_fail`.

**Formalization Note.** `H` is any probability measure on `U(d)` invariant under left and right
multiplication (`IsHaarProb`, unique). A classical-description algorithm with at most `m` samples is a
measurable acceptance function `f : U(d)^m → [0, 1]`. -/
theorem theorem_5_1 (d : ℕ) (hd : 2 ≤ d) (εfar δ : ℝ) (hε0 : 0 < εfar) (hε1 : εfar < 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (H : Measure (U d)) (hH : IsHaarProb H) (m : ℕ) :
    ¬ ∃ f : (Fin m → U d) → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => H) ∧
      ∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], εfar < tvDist H ν →
        ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ := by sorry

end DesignTest.Supplement
