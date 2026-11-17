-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_22
-- name    : DesignTest.Supplement.theorem_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:15:43.664198+00:00
-- url     : https://prove2.me/theorems/c1fe41a8-45fd-4c27-b39d-09abab572022
-- title:
--   Theorem 5.22 — Tolerant UDT on the known support $\mathcal C_d$ or $\mathcal M_d$
-- statement:
--   Let $t=2$, $d\ge2$ a prime power, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le1$, $\delta_{\mathrm{fail}}\in(0,1/2)$, $\gamma_{\mathrm{gap}}=\varepsilon_{\mathrm{far}}-\varepsilon_{\mathrm{apx}}$. Suppose every sampled oracle belongs, up to phase, to the known Clifford set $\mathcal C_d$, or to the known MUB set $\mathcal M_d$ (the support is known, its weights arbitrary). For the tolerant UDT promise there is a non-adaptive incoherent tester in the uncontrolled unitary access model with
--
--   $$m=\Big\lceil\frac{64d^4}{\gamma_{\mathrm{gap}}^2}\log\frac{4d^4}{\delta_{\mathrm{fail}}}\Big\rceil,\qquad q_{\mathrm{total}}=O\Big(m\log\frac{Lm}{\delta_{\mathrm{fail}}}\Big)\qquad(121),$$
--
--   $L=d^3(d^2-1)$ for $\mathcal C_d$ and $L=d^3(d-1)$ for $\mathcal M_d$. All queries are ancilla-free and no inverse access is used.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - generalization: the specific fields F_d ⊂ F_{d²}, the chosen basis e₁, e₂, the trace characters and the fixed phase representatives of C_d and M_d → every finite field F with |F| = d, every degree-2 extension with an F-basis, every nontrivial additive characters, every phase-representative lists; reason: the paper's construction is one such choice; the support sets do not depend on the characters, and uncontrolled-access testers do not see global phases
--   - encoding: each sampled oracle is, up to phase, in the known set → ν-almost every sample lies in the phase-closed set; reason: same instances
--   - encoding: the Haar measure H on U(d) → any H with IsHaarProb H (bi-invariant probability measure); reason: such a measure is unique
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.22, p.73-74 (PDF p.76-77)

import Mathlib
import Definitions.Def_DesignTest_Supplement_UNAI
import Definitions.Def_DesignTest_Supplement_cliffordSet
import Definitions.Def_DesignTest_Supplement_mubSet

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.22** (Tolerant UDT on `C_d` or `M_d`). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.22, eq. (121), pp.73–74.

Let `t = 2`, `d ≥ 2` a prime power, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1]`, `δ_fail ∈ (0, 1/2)`,
`γ_gap = ε_far − ε_apx`. Suppose every sampled oracle belongs, up to phase, to the known set `C_d`, or to the
known set `M_d` (the choice of support is known, its weights arbitrary). There is a non-adaptive incoherent
tester in the uncontrolled unitary access model for the tolerant UDT promise with
`m = ⌈64 d⁴/γ_gap² · log(4d⁴/δ_fail)⌉` and `q_total = O(m log(L m/δ_fail))`, `L = d³(d² − 1)` for `C_d` and
`L = d³(d − 1)` for `M_d`. All queries are ancilla-free and no inverse access is used.

**Formalization Note.** The finite fields are abstract: `F` with `|F| = d` (so `d` is a prime power) labels the basis of `ℂ^d`
through `e`, `Kf ⊇ F` with `F`-basis `b = (e₁, e₂)` is `F_{d²}`, and `χ`, `χK` are nontrivial additive characters
(the paper's trace characters are particular ones; the support sets do not depend on the choice). Support "up to phase" is `ν`-a.e. membership in `cliffordUpToPhase` /
`mubUpToPhase`. The tester is a `UNAIProc d m n 1 K` (no reference, forward calls only, `n = q_total`). One
`O` constant `C` is chosen first. -/
theorem theorem_5_22 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      ∀ (F : Type) [Field F] [DecidableEq F] (e : Fin d ≃ F) (χ : AddChar F ℂ), χ ≠ 1 →
      ∀ (Kf : Type) [Field Kf] [Algebra F Kf] (b : Module.Basis (Fin 2) F Kf) (χK : AddChar Kf ℂ), χK ≠ 1 →
      ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar → εfar ≤ 1 → 0 < δ → δ < 1 / 2 →
      ∀ H : Measure (U d), IsHaarProb H →
      (∃ m : ℕ, m = ⌈64 * (d : ℝ) ^ 4 / (εfar - εapx) ^ 2 * Real.log (4 * (d : ℝ) ^ 4 / δ)⌉₊ ∧
        ∃ n : ℕ, (n : ℝ) ≤ C * (m : ℝ) * Real.log (((d : ℝ) ^ 3 * ((d : ℝ) ^ 2 - 1)) * (m : ℝ) / δ) ∧
          ∃ (K : ℕ) (T : UNAIProc d m n 1 K), T.IsTester ∧ (∀ ω j, (T.alg ω).σ j = true) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ cliffordUpToPhase e χ) →
              twirlDist 2 H ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ cliffordUpToPhase e χ) →
              εfar < twirlDist 2 H ν → T.acceptProb ν ≤ δ)) ∧
      (∃ m : ℕ, m = ⌈64 * (d : ℝ) ^ 4 / (εfar - εapx) ^ 2 * Real.log (4 * (d : ℝ) ^ 4 / δ)⌉₊ ∧
        ∃ n : ℕ, (n : ℝ) ≤ C * (m : ℝ) * Real.log (((d : ℝ) ^ 3 * ((d : ℝ) - 1)) * (m : ℝ) / δ) ∧
          ∃ (K : ℕ) (T : UNAIProc d m n 1 K), T.IsTester ∧ (∀ ω j, (T.alg ω).σ j = true) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ mubUpToPhase e b χK) →
              twirlDist 2 H ν ≤ εapx → 1 - δ ≤ T.acceptProb ν) ∧
            (∀ (ν : Measure (U d)) [IsProbabilityMeasure ν], (∀ᵐ V ∂ν, V ∈ mubUpToPhase e b χK) →
              εfar < twirlDist 2 H ν → T.acceptProb ν ≤ δ)) := by sorry

end DesignTest.Supplement
