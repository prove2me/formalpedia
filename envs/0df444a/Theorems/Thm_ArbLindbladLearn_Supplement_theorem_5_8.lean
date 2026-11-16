-- Prove2me | Theorems.Thm_ArbLindbladLearn_Supplement_theorem_5_8
-- name    : ArbLindbladLearn.Supplement.theorem_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:26:12.606388+00:00
-- url     : https://prove2.me/theorems/9dc8c4bd-a24b-49a7-a2cb-3aee304743e2
-- title:
--   Theorem 5.8 — lower bound $\sup_{\mathcal L}\mathbb E_{\mathcal L}T_{\mathrm{tot}}=\Omega(n\Lambda_{\mathrm{loc}}/\varepsilon^2)$ on the expected total evolution time for local Lindbladians
-- statement:
--   There is an absolute constant $c_0>0$ such that for every $n\ge3$, every $\Lambda_{\mathrm{loc}}>0$ and every $0<\varepsilon\le\Lambda_{\mathrm{loc}}/2048$ there are two $n$-qubit Lindbladians $\mathcal L_+$, $\mathcal L_-$ with the following properties:
--   1. both are $3$-local and have local dynamical strength at most $\Lambda_{\mathrm{loc}}$;
--   2. they have identical Hamiltonian and dissipative supports;
--   3. there is a single-qubit Pauli label $a_0$ with $|h^+_{a_0}-h^-_{a_0}|>2\varepsilon$;
--   4. every adaptive protocol, with arbitrary ancillas, entangled inputs and quantum memory and with a possibly unbounded random number of queries to $e^{t\mathcal L}\otimes\mathrm{id}$, that stops and answers "+" with probability at least $2/3$ under $\mathcal L_+$ and stops and answers "−" with probability at least $2/3$ under $\mathcal L_-$ satisfies
--   $$\max\big(\mathbb E_{\mathcal L_+}T_{\mathrm{tot}},\ \mathbb E_{\mathcal L_-}T_{\mathrm{tot}}\big)\ \ge\ c_0\,\frac{n\Lambda_{\mathrm{loc}}}{\varepsilon^2},$$
--   where $T_{\mathrm{tot}}$ is the sum of the evolution times of the queries made.
--
--   In particular, for every $k\ge3$, any algorithm that estimates the Hamiltonian coefficients of every $k$-local $n$-qubit Lindbladian with local dynamical strength at most $\Lambda_{\mathrm{loc}}$ to entrywise error $\varepsilon$ with success probability at least $2/3$ has $\sup_{\mathcal L}\mathbb E_{\mathcal L}T_{\mathrm{tot}}=\Omega(n\Lambda_{\mathrm{loc}}/\varepsilon^2)$, even when it knows the support. The bound matches the total evolution time of Theorem 1.2 up to polylogarithmic factors.
--
--   **Formalization Note** Protocols are `OpenProtocol` (adaptive, with a stopping rule and no query bound) with `OpenAdmissible`; success is the probability of stopping with the correct decision and the expected total evolution time takes values in $[0,\infty]$. Outcome spaces range over `Type`.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: an n-qubit Lindbladian ℒ of the form (8), γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the published generator gen c; reason: ℒ is determined by its coefficients and every such coefficient vector gives a Lindbladian; same instances
--   - generalization: every algorithm that estimates the Hamiltonian coefficients of every k-local n-qubit Lindbladian with local strength ≤ Λ_loc to error ε with probability ≥ 2/3 has sup_ℒ 𝔼_ℒ T_tot = Ω(nΛ_loc/ε²) → for each n, Λ_loc, ε a fixed pair of valid 3-local Lindbladians with local strength ≤ Λ_loc, identical supports and a weight-one label a₀ with |h₊(a₀) − h₋(a₀)| > 2ε, such that every admissible open-ended protocol deciding true w.p. ≥ 2/3 under the first and false w.p. ≥ 2/3 under the second has max(𝔼₊T_tot, 𝔼₋T_tot) ≥ c₀nΛ_loc/ε²; reason: the form of Theorem 1.3 and of the proof; the maximum over the two instances is at most sup_ℒ, 3-local implies k-local for k ≥ 3, and an ε-estimator of h_{a₀} thresholded at the midpoint is such a protocol
--   - reading: n-qubit, with n unrestricted in the printed statement → n ≥ 3; reason: Theorems 5.7 and 5.8 are the formal versions of Theorem 1.3 (p.4), which assumes n ≥ 3; the hard instances need m = n − 1 ≥ 2 bath qubits (Lemma 5.1, p.36)
--   - reading: Ω(·) → ∃ an absolute constant c₀ > 0, chosen before n, Λ_loc and ε; reason: the meaning of Ω; the proof gives explicit constants
--   - encoding: k-local Lindbladian; local dynamical strength at most Λ_loc (p.2) → IsKLocal 3, and LocalStrengthLE c Λ_loc: for every qubit i, Σ_{S∋i} ‖(gen (coordPart c S))ᴴ‖_{∞→∞} ≤ Λ_loc with the induced spectral norm indNorm; reason: the paper's definitions (§1.1, pp.2–3); a 3-local generator is k-local for every k ≥ 3
--   - encoding: adaptive algorithms with arbitrary ancillas, entangled inputs, quantum memory, possibly with a random number of queries and no finite worst-case bound (proof, p.48); 𝔼_ℒ T_tot → OpenProtocol (the public protocol's fields with a stopping rule instead of a query count) with OpenAdmissible; decisionProbability (probability of stopping with the decision) and expectedTime in ℝ≥0∞; outcome spaces in Type; reason: the access model of the proof; unfinished runs never decide, and 𝔼 T_tot = ∞ is allowed
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Theorem 5.8, p.46 (pdf p.48), eq. (54); proof pp.46–48; Theorem 1.3, p.4; Lemma 5.1, p.36

import Mathlib
import Definitions.Def_ArbLindbladLearn_gen
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs
import Definitions.Def_ArbLindbladLearn_Supplement_IsKLocal
import Definitions.Def_ArbLindbladLearn_Supplement_LocalStrengthLE
import Definitions.Def_ArbLindbladLearn_Supplement_SameSupport
import Definitions.Def_ArbLindbladLearn_Supplement_OpenAdmissible
import Definitions.Def_ArbLindbladLearn_Supplement_decisionProbability
import Definitions.Def_ArbLindbladLearn_Supplement_expectedTime

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- Theorem 5.8 (Lower bound on expected total evolution time; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.46). Let `k ≥ 3`,
`Λ_loc > 0`, and `0 < ε ≤ Λ_loc/2048`. Suppose an algorithm estimates the Hamiltonian coefficients of
every `k`-local `n`-qubit Lindbladian with local dynamical strength at most `Λ_loc` to entrywise error
`ε`, with success probability at least `2/3`. Then `sup_ℒ 𝔼_ℒ T_tot = Ω(nΛ_loc/ε²)` (54). This bound
holds even for adaptive algorithms with arbitrary ancillas, entangled inputs, quantum memory, and
knowledge of the support.

**Formalization Note**
1. Stated for a pair of hard instances, as in Theorem 5.7 and Theorem 1.3 (p.4): there is an
   absolute `c₀ > 0` such that for every `n ≥ 3`, `Λ_loc > 0` and `0 < ε ≤ Λ_loc/2048` there are two
   valid 3-local Lindbladians with local strength at most `Λ_loc`, identical supports and a
   weight-one label `a₀` with `|h₊(a₀) − h₋(a₀)| > 2ε`, such that every protocol that decides
   `true` with probability `≥ 2/3` under `c₊` and `false` with probability `≥ 2/3` under `c₋` has
   `max(𝔼₊ T_tot, 𝔼₋ T_tot) ≥ c₀nΛ_loc/ε²`. Since the maximum over the two instances is at most
   `sup_ℒ`, and an `ε`-estimator of `h_{a₀}` thresholded at the midpoint is such a protocol, this
   implies the printed statement for every `k ≥ 3`.
2. Protocols may have no finite worst-case query bound (proof, p.48): `OpenProtocol` (an adaptive
   protocol with a stopping rule, arbitrary finite history-dependent quantum memory, CP instruments
   with measurable outcomes, a final two-outcome measurement), `OpenAdmissible`. Success is the
   probability of halting with the correct decision (`decisionProbability`), and `𝔼 T_tot` is
   `expectedTime`, in `ℝ≥0∞` (it may be `∞`). Outcome spaces range over `Type`. -/
theorem theorem_5_8 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ n : ℕ, 3 ≤ n → ∀ Λloc ε : ℝ, 0 < Λloc → 0 < ε → ε ≤ Λloc / 2048 →
      ∃ cp cm : Coeffs n,
        IsLindbladCoeffs cp ∧ IsLindbladCoeffs cm ∧
        IsKLocal 3 cp ∧ IsKLocal 3 cm ∧
        LocalStrengthLE cp Λloc ∧ LocalStrengthLE cm Λloc ∧
        SameSupport cp cm ∧
        ∃ a₀ : Pauli n, weight a₀ = 1 ∧ 2 * ε < |cp.h a₀ - cm.h a₀| ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (p : OpenProtocol n Ω), OpenAdmissible p →
          (2 / 3 : ℝ≥0∞) ≤ decisionProbability p (gen cp) true →
          (2 / 3 : ℝ≥0∞) ≤ decisionProbability p (gen cm) false →
          ENNReal.ofReal (c₀ * (n : ℝ) * Λloc / ε ^ 2) ≤
            max (expectedTime p (gen cp)) (expectedTime p (gen cm)) := by sorry

end ArbLindbladLearn.Supplement
