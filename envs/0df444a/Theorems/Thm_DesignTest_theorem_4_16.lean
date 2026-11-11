-- Prove2me | Theorems.Thm_DesignTest_theorem_4_16
-- name    : DesignTest.theorem_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:50.327178+00:00
-- url     : https://prove2.me/theorems/bbbbc5d4-beba-4f91-b234-5fbbb9a3c02a
-- title:
--   Theorem 4.16 — a uniform exact design on $L$ states gives $m\ge(1-2\delta_{\mathrm{fail}})\lfloor D_{\mathrm{Sym}}/2\rfloor^{3/2}/(16L\varepsilon_{\mathrm{far}}^2)$
-- statement:
--   Let $d\ge2$, $t\ge1$, $\varepsilon_{\mathrm{apx}}\in[0,\varepsilon_{\mathrm{far}})$, $\varepsilon_{\mathrm{far}}\in(0,1/4]$ and $\delta_{\mathrm{fail}}\in[0,1/2)$, and suppose the uniform measure $\nu_0=L^{-1}\sum_{j=1}^{L}\delta_{\varphi_j}$ on a list of $L$ pure states is an exact state $t$-design. Consider a tester that sees the list index $j\in[L]$ of each of its $m$ samples, i.e. a function $f:[L]^m\to[0,1]$, and is correct on the inputs supported on the list: for every probability vector $w$ on $[L]$, with $\nu_w=\sum_jw_j\delta_{\varphi_j}$,
--   1. if $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu_w)\le\varepsilon_{\mathrm{apx}}$ then $\mathbb E_{w^{\otimes m}}[f]\ge1-\delta_{\mathrm{fail}}$;
--   2. if $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu_w)>\varepsilon_{\mathrm{far}}$ then $\mathbb E_{w^{\otimes m}}[f]\le\delta_{\mathrm{fail}}$.
--
--   Then
--   $$m\ge\frac{(1-2\delta_{\mathrm{fail}})\lfloor D_{\mathrm{Sym}}/2\rfloor^{3/2}}{16L\varepsilon_{\mathrm{far}}^2}=\Omega_t\Big(\frac{(1-2\delta_{\mathrm{fail}})d^{3t/2}}{L\varepsilon_{\mathrm{far}}^2}\Big).$$
--
--   With a small design ($L=O(D_{\mathrm{Sym}})$) this is an inverse-square bound in $\varepsilon_{\mathrm{far}}$, even for testers that learn list indices and classical descriptions and use arbitrarily many queries.
--
--   **Formalization Note** Under $\nu_w$ the list indices of the samples are i.i.d. with law $w$, and the index determines the sampled state, its description and all query outcomes' laws; so a tester with the paper's strengthened interface is a function of the indices. The expectations are finite sums.
--
--   Differences from the source:
--   - generalization: any tester for (t, ε_apx, ε_far, δ_fail)-SDT, correct on every promised input → correctness required only on the promised inputs supported on the list φ_1, …, φ_L; reason: a weaker hypothesis: every SDT tester is in particular correct on these inputs
--   - generalization: each sample reveals its list index and a complete classical description, with arbitrarily many queries → the tester is any function f : (Fin m → Fin L) → [0, 1] of the m list indices; reason: the list is fixed and known, so the index determines everything the strengthened interface reveals; every such tester induces such an f
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
--   - encoding: trace norm ‖A‖₁ = Tr|A| → DistQuantumQuery.traceNorm A = Σ_i √λ_i(A†A), the sum of the singular values; reason: the same quantity, written without a square root of an operator
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.16, eq. (73), p.43

import Mathlib
import Definitions.Def_DesignTest_momentDist

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Theorem 4.16** (Sample lower bound from a finite uniform exact design). A. Kawachi, Y. Nakata,
Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.16,
eq. (73), p.43.

Let `d ≥ 2`, `t ≥ 1`, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1/4]`, `δ_fail ∈ [0, 1/2)`, and suppose the
uniform measure on a list `φ_1, …, φ_L` of pure states is an exact state `t`-design. Every tester that
sees the list index of each of its `m` samples and is correct on the inputs supported on the list (it
accepts with probability `≥ 1 − δ_fail` every list-supported `ν` with `Dist₁^{(t)}(H, ν) ≤ ε_apx`, and with
probability `≤ δ_fail` every list-supported `ν` with `Dist₁^{(t)}(H, ν) > ε_far`) satisfies
`m ≥ (1 − 2δ_fail)⌊D_Sym/2⌋^{3/2}/(16 L ε_far²)`.

**Formalization Note.** The paper's strengthened interface reveals the list index and the classical
description of every sample, with arbitrarily many queries; since the list is fixed and known, the index
determines everything, and the tester is a function `f : (Fin m → Fin L) → [0, 1]` of the `m` indices.
A list-supported input is `Σ_j w_j δ_{φ_j}` for a probability vector `w`, under which the indices are
i.i.d. with law `w`. Requiring correctness only on list-supported inputs and letting `f` see indices both
make the statement stronger than the printed one. -/
theorem theorem_4_16 (d t : ℕ) (hd : 2 ≤ d) (ht : 1 ≤ t) (εapx εfar δ : ℝ) (ha0 : 0 ≤ εapx)
    (haf : εapx < εfar) (hf1 : εfar ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (L : ℕ)
    (φ : Fin L → PureVec d) (hdesign : momentDist t (haarState d) (unifList φ) = 0) (m : ℕ)
    (f : (Fin m → Fin L) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hyes : ∀ w : Fin L → ℝ, (∀ j, 0 ≤ w j) → ∑ j, w j = 1 →
      momentDist t (haarState d) (∑ j, ENNReal.ofReal (w j) • Measure.dirac (φ j)) ≤ εapx →
      1 - δ ≤ ∑ x : Fin m → Fin L, f x * ∏ i : Fin m, w (x i))
    (hno : ∀ w : Fin L → ℝ, (∀ j, 0 ≤ w j) → ∑ j, w j = 1 →
      εfar < momentDist t (haarState d) (∑ j, ENNReal.ofReal (w j) • Measure.dirac (φ j)) →
      ∑ x : Fin m → Fin L, f x * ∏ i : Fin m, w (x i) ≤ δ) :
    (1 - 2 * δ) * ((DSym d t / 2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) / (16 * (L : ℝ) * εfar ^ 2) ≤ (m : ℝ) := by sorry

end DesignTest
