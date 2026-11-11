-- Prove2me | Theorems.Thm_BatchStabilizer_Learning_proper_agnostic_learning
-- name    : BatchStabilizer.Learning.proper_agnostic_learning
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:40:47.412135+00:00
-- url     : https://prove2.me/theorems/b85ae1b2-ab4e-4477-9009-99754291f7a4
-- title:
--   Theorem 1.1 — polynomial-copy proper agnostic stabilizer learning
-- statement:
--   Let $\rho$ be an arbitrary $n$-qubit density operator, $n\ge1$, with optimal stabilizer fidelity $F(\rho)=\max_{\phi\text{ stabilizer}}\langle\phi|\rho|\phi\rangle$. Given $0<\tau\le1/2$ with $F(\rho)\ge\tau$, $0<\varepsilon\le1$ and $0<\delta<1/3$, Algorithm 5 outputs a classical description of an $n$-qubit stabilizer state $\hat\phi$ with
--   $$\langle\hat\phi|\rho|\hat\phi\rangle\ge F(\rho)-\varepsilon$$
--   with probability at least $1-\delta$. Its worst-case quantum copy complexity is
--   $$N=O\!\left(\frac n{\tau^2}+\frac{\ln(8/\delta)}{\tau^3}+\frac{(1+\ln(1/\tau))^2+\ln(8/\delta)}{\varepsilon^2}\right)$$
--   and its classical running time is $\operatorname{poly}(n,\varepsilon^{-1},\ln(8/\delta))\exp(O((1+\ln(1/\tau))^2))$. All quantum measurements act on at most two copies of $\rho$ at a time.
--
--   Precisely: there are absolute constants $C_N,C_T,C_E>0$ and a degree $d$, fixed before all inputs, such that for all admissible $n,\tau,\varepsilon,\delta$ the learner succeeds as above for every such $\rho$, and on every transcript its output is a stabilizer state, it consumes at most $C_N[n/\tau^2+\ell/\tau^3+(h^2+\ell)/\varepsilon^2]$ copies and performs at most $C_T(1+n+\varepsilon^{-1}+\ell)^d\exp(C_Eh^2)$ classical operations, where $h=1+\ln(1/\tau)$ and $\ell=\ln(8/\delta)$. The learner sees only classical measurement records; it never receives $\rho$, an optimal stabilizer state or its label space.
--
--   Differences from the source:
--   - encoding: an n-qubit state ρ on (ℂ²)^{⊗n} → a matrix ρ : Op (Qubits n) indexed by Boolean strings with IsDensity ρ (positive semidefinite, trace one); bits of F₂ⁿ are converted by toQubits/ofQubits; reason: the same density operators in the computational basis
--   - generalization: there is an algorithm → the defined Algorithm 5 (algorithm5 n τ ε δ) satisfies all clauses; reason: the defined learner is a witness of the existential; it does not depend on ρ
--   - encoding: O(·) and poly(·)exp(O(·)) bounds → absolute constants C_N, C_T, C_E > 0 and a degree d quantified before n, τ, ε, δ and ρ; reason: the uniform meaning of the source's asymptotic notation
--   - encoding: classical running time → an explicit stage-by-stage count of bit and arithmetic operations computed from the realized list sizes (Learner definition); reason: §9.4 bounds the running time by exactly these operation counts
--   - encoding: all quantum measurements act on at most two copies of ρ at a time → the learner is a measurement program whose only quantum steps are two-copy Bell measurements and single-copy measurements; reason: the program type admits no other measurement
--   - encoding: worst-case quantum copy complexity → a bound on the copies consumed on every transcript, including every abort branch; reason: the worst case over all records
--   - encoding: a classical description of a stabilizer state → the output projector, required to lie in Stab_n on every transcript; reason: the projector is the state up to global phase and is computed from a signed tableau
--   - reading: L is the union of the a seed lists (Algorithm 5, line 2) → the concatenation of the a lists, counted with multiplicity, also in |L| inside v₄; reason: a multiset union keeps every listed seed; the larger |L| only enlarges v₄ and m₄, and |L| ≤ B_max as in §9.3
--   - encoding: the sufficiently large absolute constant in N_sh (111) → groups of ⌈48/ε²⌉ records, 2⌈4 ln(8M_max/δ)⌉+1 groups; reason: an explicit admissible choice of the source's constant
--   - encoding: Algorithm 5 lines 20–23 (assign each T' to a representative T_i with dim(T' ∩ T_i) ≥ n − t, then repeat the cap |ℛ| > 4/τ²) and line 31 (any arg max) → T' is assigned to the first such T_i in the greedy order, the second (identical) cap is omitted, and ties in the arg max go to the earliest candidate; reason: the repeated cap tests the same condition as lines 17–19 and never fires; the source leaves the assignment and the tie rule free, and every choice satisfies its analysis
-- source:
--   Ching-Yi Lai, STOC 2027 submission #1629 (October 2026), p. 3 (PDF p. 4), Theorem 1.1, equations (3)–(4)

import Mathlib
import Definitions.Def_BatchStabilizer_Learning_Learner

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix Kronecker
open LindbladTolerant.Testing

namespace BatchStabilizer.Learning

/-- Theorem 1.1, printed p. 3 (PDF p. 4): polynomial-copy proper agnostic stabilizer learning.
There are absolute constants `C_N, C_T, C_E > 0` and a degree `d` such that for all `n ≥ 1`,
`0 < τ ≤ 1/2`, `0 < ε ≤ 1`, `0 < δ < 1/3`, Algorithm 5 — which only sees classical records of
two-copy Bell measurements and single-copy measurements of the unknown state — outputs, for every
density matrix `ρ` with `F(ρ) ≥ τ`, a stabilizer state with `⟨ϕ̂|ρ|ϕ̂⟩ ≥ F(ρ) - ε` with
probability at least `1 - δ`; and on every transcript its output is a stabilizer state, it uses
at most `C_N (n/τ² + ln(8/δ)/τ³ + ((1 + ln(1/τ))² + ln(8/δ))/ε²)` copies (3), and at most
`C_T (1 + n + ε⁻¹ + ln(8/δ))^d exp(C_E (1 + ln(1/τ))²)` classical operations (4). -/
theorem proper_agnostic_learning :
    ∃ (CN CT CE : ℝ) (d : ℕ), 0 < CN ∧ 0 < CT ∧ 0 < CE ∧
      ∀ n : ℕ, 1 ≤ n → ∀ τ ε δ : ℝ, 0 < τ → τ ≤ 1 / 2 → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 / 3 →
        (∀ ρ : Op (Qubits n), IsDensity ρ → τ ≤ stabFidelity ρ →
          1 - δ ≤ (algorithm5 n τ ε δ).prob ρ
            (fun out => stabFidelity ρ - ε ≤ (ρ * out.1).trace.re)) ∧
        (algorithm5 n τ ε δ).allRuns (fun copies out =>
          out.1 ∈ ArbLindbladLearn.Stab n ∧
          (copies : ℝ) ≤ CN * ((n : ℝ) / τ ^ 2 + Real.log (8 / δ) / τ ^ 3 +
            ((1 + Real.log (1 / τ)) ^ 2 + Real.log (8 / δ)) / ε ^ 2) ∧
          (out.2 : ℝ) ≤ CT * (1 + (n : ℝ) + ε⁻¹ + Real.log (8 / δ)) ^ d *
            Real.exp (CE * (1 + Real.log (1 / τ)) ^ 2)) := by sorry

end BatchStabilizer.Learning
