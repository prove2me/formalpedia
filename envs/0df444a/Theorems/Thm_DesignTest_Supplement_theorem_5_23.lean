-- Prove2me | Theorems.Thm_DesignTest_Supplement_theorem_5_23
-- name    : DesignTest.Supplement.theorem_5_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:16:17.826794+00:00
-- url     : https://prove2.me/theorems/0dd201ba-4e73-488d-90e1-275eb7718986
-- title:
--   Theorem 5.23 — Upper bounds for uniform-versus-subset instances on $\mathcal C_d$ and $\mathcal M_d$
-- statement:
--   Let $d\ge4$ be a prime power, $0\le\varepsilon_{\mathrm{apx}}<\varepsilon_{\mathrm{far}}\le1/4$, $\delta_{\mathrm{fail}}\in(0,1/2)$, $M=\lfloor d^3(d-1)/4\rfloor$ and $\lambda=4\varepsilon_{\mathrm{far}}$. For a known uniform distribution $\mu_0$ on a list of distinct projective matrices, let $q_S$ be uniform on an unknown fixed size-$M$ subset $S$ of the list, and consider the promise $\nu=\mu_0$ (accept) or $\nu=(1-\lambda)\mu_0+\lambda q_S$ (reject).
--
--   1. For $\mu_0=\mu_C$ a tester uses $m=O([d^{3/2}\varepsilon_{\mathrm{far}}^{-2}+d^2\varepsilon_{\mathrm{far}}^{-1}]\log(1/\delta_{\mathrm{fail}}))$ samples (122).
--   2. For $\mu_0=\mu_{\mathrm{MUB}}$, provided $\varepsilon_{\mathrm{apx}}\ge2/(d+1)$, it uses $m=O(d^2\varepsilon_{\mathrm{far}}^{-2}\log(1/\delta_{\mathrm{fail}}))$ samples (123).
--
--   In either case $q_{\mathrm{total}}=O(m\log(dm/\delta_{\mathrm{fail}}))$, and the tester is non-adaptive incoherent in the uncontrolled unitary access model and ancilla-free. Correctness is asserted only for this restricted family; one tester must work for every subset $S$.
--
--   Differences from the source:
--   - encoding: O(·) / Ω(·) with universal implicit constants → ∃ C > 0 chosen before every other parameter; reason: the theorem states the constants are universal
--   - generalization: the specific fields F_d ⊂ F_{d²}, the chosen basis e₁, e₂, the trace characters and the fixed phase representatives of C_d and M_d → every finite field F with |F| = d, every degree-2 extension with an F-basis, every nontrivial additive characters, every phase-representative lists; reason: the paper's construction is one such choice; the support sets do not depend on the characters, and uncontrolled-access testers do not see global phases
--   - encoding: algorithms with internal randomness and quantum measurements → RandProc: arbitrary measurable seed space, finite-outcome measurements, output function of seed and transcript; reason: a continuous-outcome measurement in finite dimension is a randomization of finite-outcome ones plus post-processing (Chiribella–D'Ariano–Schlingemann 2007); finite-dimensional strategies have finite-outcome classical control
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.23, p.74-75 (PDF p.77-78)

import Mathlib
import Definitions.Def_DesignTest_Supplement_tvDist
import Definitions.Def_DesignTest_Supplement_UNAI
import Definitions.Def_DesignTest_Supplement_cliffordSet
import Definitions.Def_DesignTest_Supplement_mubSet

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound

/-- **Theorem 5.23** (Upper bounds for subset instances on `C_d` and `M_d`). A. Kawachi, Y. Nakata, Y. Takeuchi, *Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Theorem 5.23,
eqs. (122)–(123), pp.74–75.

Let `d ≥ 4` be a prime power, `ε_apx ∈ [0, ε_far)`, `ε_far ∈ (0, 1/4]`, `δ_fail ∈ (0, 1/2)`; set
`M = ⌊d³(d − 1)/4⌋` and `λ = 4ε_far`. For a known uniform distribution `μ₀` on a list of distinct projective
matrices, let `q_S` be uniform on any unknown fixed size-`M` subset of its list, and consider the promise
`ν = μ₀` or `ν = (1 − λ)μ₀ + λ q_S`. For `μ₀ = μ_C` a tester uses `m = O([d^{3/2}/ε_far² + d²/ε_far] log(1/δ_fail))`
(122); for `μ₀ = μ_MUB`, provided `ε_apx ≥ 2/(d + 1)`, it uses `m = O(d²/ε_far² · log(1/δ_fail))` (123). In
either case `q_total = O(m log(d m/δ_fail))`; the tester is non-adaptive incoherent in the uncontrolled
unitary access model and ancilla-free. Correctness is asserted only for this restricted family.

**Formalization Note.** The finite fields are abstract: `F` with `|F| = d` (so `d` is a prime power) labels the basis of `ℂ^d`
through `e`, `Kf ⊇ F` with `F`-basis `b = (e₁, e₂)` is `F_{d²}`, and `χ`, `χK` are nontrivial additive characters
(the paper's trace characters are particular ones; the support sets do not depend on the choice). The lists are any one-phase-representative choices `R_C`, `R_M` of the
projective sets (`IsPhaseReps`); the tester may depend on the known list but not on `S`: one tester must
accept `μ₀` and reject `(1 − λ)μ₀ + λ q_S` for every `S` of size `M` (natural-number floor). Ancilla-free is
`w = 1`. One `O` constant `C` is chosen first. -/
theorem theorem_5_23 :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 4 ≤ d →
      ∀ (F : Type) [Field F] [DecidableEq F] (e : Fin d ≃ F) (χ : AddChar F ℂ), χ ≠ 1 →
      ∀ (Kf : Type) [Field Kf] [Algebra F Kf] (b : Module.Basis (Fin 2) F Kf) (χK : AddChar Kf ℂ), χK ≠ 1 →
      ∀ εapx εfar δ : ℝ, 0 ≤ εapx → εapx < εfar → εfar ≤ 1 / 4 → 0 < δ → δ < 1 / 2 →
      (∀ RC : Finset (U d), IsPhaseReps RC (cliffordUpToPhase e χ) →
          ∃ m : ℕ, (m : ℝ) ≤ C * ((d : ℝ) ^ ((3 : ℝ) / 2) / εfar ^ 2 + (d : ℝ) ^ 2 / εfar) * Real.log (1 / δ) ∧
            ∃ n : ℕ, (n : ℝ) ≤ C * (m : ℝ) * Real.log ((d : ℝ) * (m : ℝ) / δ) ∧
            ∃ (K : ℕ) (T : UNAIProc d m n 1 K), T.IsTester ∧
              1 - δ ≤ T.acceptProb (unifFinset RC) ∧
              ∀ S : Finset (U d), S ⊆ RC → S.card = d ^ 3 * (d - 1) / 4 →
                T.acceptProb (ENNReal.ofReal (1 - 4 * εfar) • unifFinset RC +
                  ENNReal.ofReal (4 * εfar) • unifFinset S) ≤ δ) ∧
      (2 / ((d : ℝ) + 1) ≤ εapx → ∀ RM : Finset (U d), IsPhaseReps RM (mubUpToPhase e b χK) →
          ∃ m : ℕ, (m : ℝ) ≤ C * ((d : ℝ) ^ 2 / εfar ^ 2) * Real.log (1 / δ) ∧
            ∃ n : ℕ, (n : ℝ) ≤ C * (m : ℝ) * Real.log ((d : ℝ) * (m : ℝ) / δ) ∧
            ∃ (K : ℕ) (T : UNAIProc d m n 1 K), T.IsTester ∧
              1 - δ ≤ T.acceptProb (unifFinset RM) ∧
              ∀ S : Finset (U d), S ⊆ RM → S.card = d ^ 3 * (d - 1) / 4 →
                T.acceptProb (ENNReal.ofReal (1 - 4 * εfar) • unifFinset RM +
                  ENNReal.ofReal (4 * εfar) • unifFinset S) ≤ δ) := by sorry

end DesignTest.Supplement
