-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_4_1
-- name    : DesignTest.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:08:35.756868+00:00
-- url     : https://prove2.me/theorems/7b666ac6-0c75-4077-a523-38909c2c5398
-- title:
--   Theorem 4.1 — Impossibility of Haar state testing in TV distance
-- statement:
--   Let $d\ge2$, $\varepsilon_{\mathrm{far}}\in(0,1)$ and $\delta_{\mathrm{fail}}\in[0,1/2)$. Let $H$ be the Haar measure on the pure states $P(d)$. For every integer $m\ge0$ there is **no** test that receives the classical descriptions $|\psi_1\rangle\langle\psi_1|,\dots,|\psi_m\rangle\langle\psi_m|$ of $m$ independent samples from an unknown probability measure $\nu$ on $P(d)$ and satisfies both
--
--   $$\Pr[\text{accept}\mid\nu=H]\ge1-\delta_{\mathrm{fail}},\qquad \Pr[\text{accept}\mid\nu]\le\delta_{\mathrm{fail}}\ \text{ whenever }\ \mathrm{Dist}_{\mathrm{TV}}(H,\nu)>\varepsilon_{\mathrm{far}} .$$
--
--   No finite number of samples suffices to test Haar randomness of states in total variation, which motivates testing only the first $t$ moments.
--
--   **Formalization Note.** A test is a measurable acceptance function $f:P(d)^m\to[0,1]$; the NO inputs are all Borel probability measures on $P(d)$.
--
--   Differences from the source:
--   - encoding: classical-description algorithm making at most m sample requests, with arbitrary processing and internal randomness → measurable f : X^m → [0, 1] (acceptance probability); reason: samples may be drawn in advance (§3.2, p.14); averaging internal randomness and measurements gives f
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.1, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_DesignTest_Supplement_tvDist
import Definitions.Def_DesignTest_Supplement_PState

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory

/-- **Theorem 4.1** (Impossibility of Haar state testing in TV distance). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.1, p.22.

Fix `d ≥ 2`, `ε_far ∈ (0, 1)` and `δ_fail ∈ [0, 1/2)`. For every `m ≥ 0` there is no test given the
classical descriptions `|ψ_1⟩⟨ψ_1|, …, |ψ_m⟩⟨ψ_m|` of `m` independent samples from `ν` that accepts
`ν = H` with probability at least `1 − δ_fail` and accepts every `ν` with `Dist_TV(H, ν) > ε_far` with
probability at most `δ_fail`.

**Formalization Note.** Inputs are probability measures on `P(d)` (rank-one projectors), `H` is the Haar
measure on `P(d)` (`haarProj`). In the classical-description model (Definition 3.9) an algorithm using
at most `m` samples may draw them in advance, so it is a measurable acceptance function
`f : P(d)^m → [0, 1]` (internal randomness and quantum processing averaged in). -/
theorem theorem_4_1 (d : ℕ) (hd : 2 ≤ d) (εfar δ : ℝ) (hε0 : 0 < εfar) (hε1 : εfar < 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (m : ℕ) :
    ¬ ∃ f : (Fin m → PState d) → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      1 - δ ≤ ∫ x, f x ∂(Measure.pi fun _ : Fin m => haarProj d) ∧
      ∀ (ν : Measure (PState d)) [IsProbabilityMeasure ν], εfar < tvDist (haarProj d) ν →
        ∫ x, f x ∂(Measure.pi fun _ : Fin m => ν) ≤ δ := by sorry

end DesignTest.Supplement
