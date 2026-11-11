-- Prove2me | Theorems.Thm_DesignTest_theorem_4_11
-- name    : DesignTest.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:34.319659+00:00
-- url     : https://prove2.me/theorems/920f0d7c-4803-4006-ad1a-c5d2d0e89088
-- title:
--   Theorem 4.11 — exact SDT with $m=O(\sqrt{D_{\mathrm{Sym}}}/\varepsilon_{\mathrm{far}}^2\log\frac1{\delta})$ samples and $q=O(tD_{\mathrm{Sym}}^{3/2}/\varepsilon_{\mathrm{far}}^2)$ queries per sample
-- statement:
--   There is a universal constant $C>0$ such that for every $d\ge2$, $t\ge1$, $\varepsilon_{\mathrm{far}}\in(0,1]$ and $\delta_{\mathrm{fail}}\in(0,1/2)$ there exist $m,q$ with
--   $$m\le C\,\frac{\sqrt{D_{\mathrm{Sym}}}}{\varepsilon_{\mathrm{far}}^2}\log\frac1{\delta_{\mathrm{fail}}},\qquad q\le C\,\frac{t\,D_{\mathrm{Sym}}^{3/2}}{\varepsilon_{\mathrm{far}}^2},\qquad mq\le C\,\frac{t\,D_{\mathrm{Sym}}^{2}}{\varepsilon_{\mathrm{far}}^4}\log\frac1{\delta_{\mathrm{fail}}},$$
--   and a non-adaptive coherent tester with $m$ samples and $q$ queries per sample that solves the exact $(t,\varepsilon_{\mathrm{far}},\delta_{\mathrm{fail}})$-SDT:
--   1. it accepts every exact state $t$-design $\nu$ ($\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)=0$) with probability at least $1-\delta_{\mathrm{fail}}$;
--   2. it accepts every $\nu$ with $\mathrm{Dist}_1^{(t)}(\mathsf H,\nu)>\varepsilon_{\mathrm{far}}$ with probability at most $\delta_{\mathrm{fail}}$.
--
--   Since $D_{\mathrm{Sym}}=\Theta_t(d^t)$, this is $m=O_t(d^{t/2}/\varepsilon_{\mathrm{far}}^2\cdot\log(1/\delta_{\mathrm{fail}}))$ samples, which matches the lower bound of Theorem 4.14 in its dependence on $d$.
--
--   **Formalization Note** A non-adaptive coherent tester is a POVM effect on the $mq$ supplied copies (`NACTester`), and its acceptance probability is the expected trace against $\bigotimes_i(|\psi_i\rangle\langle\psi_i|)^{\otimes q}$ under $\nu^{\otimes m}$.
--
--   Differences from the source:
--   - encoding: pure states P(d) are rank-one density matrices |ψ⟩⟨ψ|, and inputs are probability measures on P(d) → pure states are unit vectors of ℂ^d (PureVec d) and inputs are probability measures on the unit sphere; reason: |ψ⟩⟨ψ| is determined by ψ, and every moment operator depends on ψ only through |ψ⟩⟨ψ|; every measure on P(d) lifts to the sphere
--   - encoding: H is the unique unitarily invariant probability measure on P(d) (Definition 3.10) → haarState d, the normalized surface measure on the unit sphere of ℂ^d; reason: its image under ψ ↦ |ψ⟩⟨ψ| is the unitarily invariant probability measure on P(d), so it has the same moment operators
--   - encoding: trace norm ‖A‖₁ = Tr|A| → DistQuantumQuery.traceNorm A = Σ_i √λ_i(A†A), the sum of the singular values; reason: the same quantity, written without a square root of an operator
--   - encoding: m = O(√D_Sym/ε_far² · log(1/δ_fail)), q = O(t D_Sym^{3/2}/ε_far²), q_total = O(t D_Sym²/ε_far⁴ · log(1/δ_fail)) → one constant C > 0 chosen before d, t, ε_far, δ_fail with m ≤ C√D_Sym/ε_far²·log(1/δ), q ≤ C t D_Sym^{3/2}/ε_far², m q ≤ C t D_Sym²/ε_far⁴·log(1/δ); reason: the O(·) of (56)–(58) hide an absolute constant (the t-dependence is explicit)
--   - encoding: a non-adaptive coherent tester in the state-preparation access model (Definitions 3.3, 3.5, 3.6) → a POVM effect 0 ≤ E ≤ 1 on the m q supplied copies ⊗_i (|ψ_i⟩⟨ψ_i|)^{⊗q} (NACTester); reason: for a fixed allocation the tester is a joint two-outcome POVM on the supplied state; ancillas, initial randomness and post-processing are absorbed into E, and a tester using fewer than q copies of a sample is an effect acting trivially on the unused copies
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.11, eqs. (56)–(58), p.37

import Mathlib
import Definitions.Def_DesignTest_momentDist
import Definitions.Def_DesignTest_NACTester

set_option autoImplicit false

namespace DesignTest

open MeasureTheory

/-- **Theorem 4.11** (Frame-potential bound for exact state designs). A. Kawachi, Y. Nakata, Y. Takeuchi,
*Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 4.11,
eqs. (56)–(58), p.37.

There is a universal constant `C > 0` such that for every `d ≥ 2`, `t ≥ 1`, `ε_far ∈ (0, 1]` and
`δ_fail ∈ (0, 1/2)` the exact `(t, ε_far, δ_fail)`-SDT is solved by a non-adaptive coherent tester with
`m ≤ C √D_Sym/ε_far² · log(1/δ_fail)` samples, `q ≤ C t D_Sym^{3/2}/ε_far²` queries per sample, and
`m q ≤ C t D_Sym²/ε_far⁴ · log(1/δ_fail)` queries in total: it accepts every exact state `t`-design with
probability at least `1 − δ_fail` and accepts every `ν` with `Dist₁^{(t)}(H, ν) > ε_far` with probability
at most `δ_fail`.

**Formalization Note.** The `O(·)` of (56)–(58) are one constant `C` chosen before all parameters. A
non-adaptive coherent tester is a POVM effect on the `m q` supplied copies (`NACTester`). -/
theorem theorem_4_11 :
    ∃ C : ℝ, 0 < C ∧ ∀ d t : ℕ, 2 ≤ d → 1 ≤ t → ∀ εfar δ : ℝ, 0 < εfar → εfar ≤ 1 → 0 < δ → δ < 1 / 2 →
      ∃ m q : ℕ,
        (m : ℝ) ≤ C * Real.sqrt (DSym d t : ℝ) / εfar ^ 2 * Real.log (1 / δ) ∧
        (q : ℝ) ≤ C * (t : ℝ) * (DSym d t : ℝ) ^ (3 / 2 : ℝ) / εfar ^ 2 ∧
        (m : ℝ) * (q : ℝ) ≤ C * (t : ℝ) * (DSym d t : ℝ) ^ 2 / εfar ^ 4 * Real.log (1 / δ) ∧
        ∃ T : NACTester d m q,
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              momentDist t (haarState d) ν = 0 → 1 - δ ≤ T.acceptProb ν) ∧
          (∀ (ν : Measure (PureVec d)) [IsProbabilityMeasure ν],
              εfar < momentDist t (haarState d) ν → T.acceptProb ν ≤ δ) := by sorry

end DesignTest
