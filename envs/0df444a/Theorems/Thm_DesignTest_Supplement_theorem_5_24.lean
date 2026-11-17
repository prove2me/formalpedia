-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_24
-- name    : DesignTest.Supplement.theorem_5_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:16:48.821073+00:00
-- url     : https://prove2.me/theorems/d7215db5-3265-41b0-a0de-4e330621bee4
-- title:
--   Theorem 5.24 — Upper bound for mixed $\mathcal M_d$-subset instances
-- statement:
--   Let $d\ge4$ be a prime power, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le1/4$, $\delta_{\mathrm{fail}}\in(0,1/2)$. Let $a\in(0,1]$ be known with $a\ge4\varepsilon_{\mathrm{far}}$ and $2a/(d+1)\le\varepsilon_{\mathrm{apx}}$, $\beta=4\varepsilon_{\mathrm{far}}/a$, $M=\lfloor d^3(d-1)/4\rfloor$, and $q_S$ uniform on an unknown fixed size-$M$ subset of $\mathcal M_d$. The promise
--
--   $$\nu=\mu_Y:=(1-a)\mu_C+a\mu_{\mathrm{MUB}}\quad\text{or}\quad\nu=\nu_S:=(1-a)\mu_C+a\big((1-\beta)\mu_{\mathrm{MUB}}+\beta q_S\big)$$
--
--   is tested with $m=O((a+1/d)d^2\varepsilon_{\mathrm{far}}^{-2}\log(1/\delta_{\mathrm{fail}}))$ samples and $q_{\mathrm{total}}=O(m\log(dm/\delta_{\mathrm{fail}}))$ (124), by a non-adaptive incoherent, ancilla-free tester in the uncontrolled unitary access model. No flag revealing the mixture component is given.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - generalization: the specific fields F_d ⊂ F_{d²}, the chosen basis e₁, e₂, the trace characters and the fixed phase representatives of C_d and M_d → every finite field F with |F| = d, every degree-2 extension with an F-basis, every nontrivial additive characters, every phase-representative lists; reason: the paper's construction is one such choice; the support sets do not depend on the characters, and uncontrolled-access testers do not see global phases
--   - generalization: the compatible phase representatives of Lemma 5.17 (M_d ⊆ C_d as matrices) → arbitrary phase-representative lists of C_d and M_d; reason: the paper's lists are one admissible choice; the acceptance probability of an uncontrolled-access tester does not depend on global phases
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.24, p.75 (PDF p.78)

import Mathlib
import Definitions.Def_DesignTest_Supplement_tvDist
import Definitions.Def_DesignTest_Supplement_UNAI
import Definitions.Def_DesignTest_Supplement_cliffordSet
import Definitions.Def_DesignTest_Supplement_mubSet

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.24** (Upper bound for mixed `M_d`-subset instances). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.24, eq. (124), p.75.

Let `d ≥ 4` be a prime power, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1/4]`, `δ_fail ∈ (0, 1/2)`. Suppose
`a ∈ (0, 1]` is known and `a ≥ 4ε_far`, `2a/(d + 1) ≤ ε_apx`; set `β = 4ε_far/a` and `M = ⌊d³(d − 1)/4⌋`. For `q_S`
uniform on any unknown fixed size-`M` subset of `M_d`, the promise `ν = μ_Y := (1 − a)μ_C + a μ_MUB` or
`ν = ν_S := (1 − a)μ_C + a((1 − β)μ_MUB + β q_S)` is tested with `m = O((a + 1/d) d²/ε_far² · log(1/δ_fail))` and
`q_total = O(m log(d m/δ_fail))` (124), by a non-adaptive incoherent, ancilla-free tester in the uncontrolled
unitary access model; no flag revealing the mixture component is assumed.

**Formalization Note.** The finite fields are abstract: `F` with `|F| = d` (so `d` is a prime power) labels the basis of `ℂ^d`
through `e`, `Kf ⊇ F` with `F`-basis `b = (e₁, e₂)` is `F_{d²}`, and `χ`, `χK` are nontrivial additive characters
(the paper's trace characters are particular ones; the support sets do not depend on the choice). `μ_C`, `μ_MUB` are uniform on phase-representative lists `R_C`, `R_M`. The paper
uses the compatible representatives of Lemma 5.17 (`M_d ⊆ C_d` as matrices); here the lists are arbitrary,
which covers that choice. The tester sees only samples and may depend on `a`, not on `S`. Ancilla-free
is `w = 1`. One `O` constant `C` is chosen first. -/
theorem theorem_5_24 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 4 ≤ d →
      ∀ (F : Type) [Field F] [DecidableEq F] (e : Fin d ≃ F) (χ : AddChar F ℂ), χ ≠ 1 →
      ∀ (Kf : Type) [Field Kf] [Algebra F Kf] (b : Module.Basis (Fin 2) F Kf) (χK : AddChar Kf ℂ), χK ≠ 1 →
      ∀ RC RM : Finset (U d), IsPhaseReps RC (cliffordUpToPhase e χ) →
        IsPhaseReps RM (mubUpToPhase e b χK) →
      ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar → εfar ≤ 1 / 4 → 0 < δ → δ < 1 / 2 →
      ∀ a : ℝ, 0 < a → a ≤ 1 → 4 * εfar ≤ a → 2 * a / ((d : ℝ) + 1) ≤ εapx →
        ∃ m : ℕ, (m : ℝ) ≤ C * ((a + 1 / (d : ℝ)) * (d : ℝ) ^ 2 / εfar ^ 2) * Real.log (1 / δ) ∧
          ∃ n : ℕ, (n : ℝ) ≤ C * (m : ℝ) * Real.log ((d : ℝ) * (m : ℝ) / δ) ∧
          ∃ (K : ℕ) (T : UNAIProc d m n 1 K), T.IsTester ∧
            1 - δ ≤ T.acceptProb (ENNReal.ofReal (1 - a) • unifFinset RC +
              ENNReal.ofReal a • unifFinset RM) ∧
            ∀ S : Finset (U d), S ⊆ RM → S.card = d ^ 3 * (d - 1) / 4 →
              T.acceptProb (ENNReal.ofReal (1 - a) • unifFinset RC +
                ENNReal.ofReal a • (ENNReal.ofReal (1 - 4 * εfar / a) • unifFinset RM +
                  ENNReal.ofReal (4 * εfar / a) • unifFinset S)) ≤ δ := by sorry

end DesignTest.Supplement
