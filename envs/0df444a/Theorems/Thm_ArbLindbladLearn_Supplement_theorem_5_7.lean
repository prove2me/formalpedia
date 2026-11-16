-- Prove2me | Theorems.Thm_ArbLindbladLearn_Supplement_theorem_5_7
-- name    : ArbLindbladLearn.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:24:55.340214+00:00
-- url     : https://prove2.me/theorems/a13b181a-d8f6-489e-b735-d56a2df3360e
-- title:
--   Theorem 5.7 — lower bound $N_{\mathrm{exp}}=\Omega(n^2\Lambda_{\mathrm{loc}}^2/\varepsilon^2)$ on the experiment count for estimating a Hamiltonian coefficient of a local Lindbladian
-- statement:
--   There is an absolute constant $c_0>0$ such that for every $n\ge3$, every $\Lambda_{\mathrm{loc}}>0$ and every $0<\varepsilon\le\Lambda_{\mathrm{loc}}/2048$ there are two $n$-qubit Lindbladians $\mathcal L_+$, $\mathcal L_-$ with the following properties:
--   1. both are $3$-local and have local dynamical strength at most $\Lambda_{\mathrm{loc}}$, i.e. $\max_i\sum_{S\ni i}\|\mathcal L_{\pm,S}^\dagger\|_{\infty\to\infty}\le\Lambda_{\mathrm{loc}}$;
--   2. they have identical Hamiltonian and dissipative supports;
--   3. there is a single-qubit Pauli label $a_0$ with $|h^+_{a_0}-h^-_{a_0}|>2\varepsilon$;
--   4. every adaptive protocol, with arbitrary ancillas, entangled inputs and quantum memory, that queries $e^{t\mathcal L}\otimes\mathrm{id}$ at most $N_{\mathrm{exp}}$ times (durations $t\ge0$ chosen adaptively) and answers "+" with probability at least $2/3$ under $\mathcal L_+$ and "−" with probability at least $2/3$ under $\mathcal L_-$ satisfies
--   $$N_{\mathrm{exp}}\ \ge\ c_0\,\frac{n^2\Lambda_{\mathrm{loc}}^2}{\varepsilon^2}.$$
--
--   In particular, for every $k\ge3$, any algorithm that estimates the Hamiltonian coefficients of every $k$-local $n$-qubit Lindbladian with local dynamical strength at most $\Lambda_{\mathrm{loc}}$ to entrywise error $\varepsilon$ with success probability at least $2/3$ needs $N_{\mathrm{exp}}=\Omega(n^2\Lambda_{\mathrm{loc}}^2/\varepsilon^2)$ experiments, even when it knows the support: thresholding its estimate of $h_{a_0}$ at the midpoint distinguishes the two instances. The bound matches the experiment count of Theorem 1.2 up to polylogarithmic factors.
--
--   **Formalization Note** The protocols are the public bounded-query adaptive protocols `LindbladTolerant.Testing.Protocol` with their admissibility conditions; the worst-case number of experiments is the protocol's query count (shorter branches padded with zero-duration calls). Outcome spaces range over `Type`.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: an n-qubit Lindbladian ℒ of the form (8), γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the published generator gen c; reason: ℒ is determined by its coefficients and every such coefficient vector gives a Lindbladian; same instances
--   - generalization: every algorithm that estimates the Hamiltonian coefficients of every k-local n-qubit Lindbladian with local strength ≤ Λ_loc to error ε with probability ≥ 2/3 has N_exp = Ω(n²Λ_loc²/ε²) → for each n, Λ_loc, ε a fixed pair of valid 3-local Lindbladians with local strength ≤ Λ_loc, identical supports and a weight-one label a₀ with |h₊(a₀) − h₋(a₀)| > 2ε, such that every admissible protocol answering true w.p. ≥ 2/3 under the first and false w.p. ≥ 2/3 under the second has queries ≥ c₀n²Λ_loc²/ε²; reason: the form of Theorem 1.3's last sentence and of the proof; it specializes to the printed statement for every k ≥ 3, since 3-local implies k-local and an ε-estimator of h_{a₀} thresholded at the midpoint is such a protocol
--   - reading: n-qubit, with n unrestricted in the printed statement → n ≥ 3; reason: Theorems 5.7 and 5.8 are the formal versions of Theorem 1.3 (p.4), which assumes n ≥ 3; the hard instances need m = n − 1 ≥ 2 bath qubits (Lemma 5.1, p.36)
--   - reading: Ω(·) → ∃ an absolute constant c₀ > 0, chosen before n, Λ_loc and ε; reason: the meaning of Ω; the proof gives explicit constants
--   - encoding: k-local Lindbladian; local dynamical strength at most Λ_loc (p.2) → IsKLocal 3, and LocalStrengthLE c Λ_loc: for every qubit i, Σ_{S∋i} ‖(gen (coordPart c S))ᴴ‖_{∞→∞} ≤ Λ_loc with the induced spectral norm indNorm; reason: the paper's definitions (§1.1, pp.2–3); a 3-local generator is k-local for every k ≥ 3
--   - encoding: adaptive algorithms with arbitrary ancillas, entangled inputs, quantum memory; N_exp the worst-case experiment count → the public LindbladTolerant.Testing.Protocol (history-dependent memory, durations, CP instruments with measurable outcomes, final two-outcome effect) with its Admissible conditions, and its query count; outcome spaces in Type; reason: the access model of the proof (p.45), which pads shorter branches with zero-duration calls; the admissibility conditions are physicality and the measurability needed for the run probabilities to be defined
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Theorem 5.7, p.45 (pdf p.47), eq. (52); Theorem 1.3, p.4; Lemma 5.1, p.36

import Mathlib
import Definitions.Def_ArbLindbladLearn_gen
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs
import Definitions.Def_LindbladTolerant_Testing_protocols
import Definitions.Def_ArbLindbladLearn_Supplement_IsKLocal
import Definitions.Def_ArbLindbladLearn_Supplement_LocalStrengthLE
import Definitions.Def_ArbLindbladLearn_Supplement_SameSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- Theorem 5.7 (Lower bound on experiment count; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.45). Let `k ≥ 3`, `Λ_loc > 0`, and
`0 < ε ≤ Λ_loc/2048`. Suppose an algorithm estimates the Hamiltonian coefficients of every `k`-local
`n`-qubit Lindbladian with local dynamical strength at most `Λ_loc` to entrywise error `ε`, with
success probability at least `2/3`. Then `N_exp = Ω(n²Λ_loc²/ε²)` (52). This bound holds even for
adaptive algorithms with arbitrary ancillas, entangled inputs, quantum memory, and knowledge of the
support.

**Formalization Note**
1. Stated, as in the proof and in Theorem 1.3 (p.4: "They already hold for a pair of 3-local
   generators with identical known supports when only the Hamiltonian coefficient at a specified
   single-qubit Pauli operator is estimated"), for a pair of hard instances: there is an absolute
   `c₀ > 0` such that for every `n ≥ 3` (Theorem 1.3; Lemma 5.1 needs `m = n − 1 ≥ 2`), `Λ_loc > 0`
   and `0 < ε ≤ Λ_loc/2048` there are two valid Lindbladians `gen c₊`, `gen c₋`, both 3-local with
   local strength at most `Λ_loc` and identical supports, and a weight-one label `a₀` with
   `|h₊(a₀) − h₋(a₀)| > 2ε`, such that every protocol that answers `true` with probability `≥ 2/3`
   under `c₊` and `false` with probability `≥ 2/3` under `c₋` makes at least `c₀n²Λ_loc²/ε²` queries.
   This implies the printed statement for every `k ≥ 3`: a 3-local generator is `k`-local, and an
   algorithm that estimates `h_{a₀}` to error `ε` with probability `≥ 2/3` on both instances,
   thresholded at the midpoint `(h₊(a₀) + h₋(a₀))/2`, is such a protocol.
2. The access model is the public bounded-query adaptive protocol `LindbladTolerant.Testing.Protocol`
   with its `Admissible` conditions: each query applies `e^{tℒ} ⊗ id` for a history-dependent
   `t ≥ 0` to the system and an arbitrary finite, history-dependent quantum memory (ancillas,
   entangled inputs), followed by a CP instrument with arbitrary measurable outcomes, and a final
   two-outcome measurement. `queries` is the worst-case number of experiments `N_exp` (shorter
   branches are padded with zero-duration calls, as in the proof). Outcome spaces range over
   `Type`.
3. Local strength is `LocalStrengthLE` (`max_i Σ_{S∋i} ‖ℒ_S†‖_{∞→∞} ≤ Λ_loc`, p.2), locality is
   `IsKLocal 3`, `|supp a₀| = 1` is the public `weight`. -/
theorem theorem_5_7 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ n : ℕ, 3 ≤ n → ∀ Λloc ε : ℝ, 0 < Λloc → 0 < ε → ε ≤ Λloc / 2048 →
      ∃ cp cm : Coeffs n,
        IsLindbladCoeffs cp ∧ IsLindbladCoeffs cm ∧
        IsKLocal 3 cp ∧ IsKLocal 3 cm ∧
        LocalStrengthLE cp Λloc ∧ LocalStrengthLE cm Λloc ∧
        SameSupport cp cm ∧
        ∃ a₀ : Pauli n, weight a₀ = 1 ∧ 2 * ε < |cp.h a₀ - cm.h a₀| ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (p : Protocol n Ω),
          LindbladTolerant.Testing.Admissible p →
          (2 / 3 : ℝ≥0∞) ≤ outputProbability p (gen cp) true →
          (2 / 3 : ℝ≥0∞) ≤ outputProbability p (gen cm) false →
          c₀ * (n : ℝ) ^ 2 * Λloc ^ 2 / ε ^ 2 ≤ (p.queries : ℝ) := by sorry

end ArbLindbladLearn.Supplement
