-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_sign_degree_communication_lower_bounds
-- name    : BooleanHiddenPartition.LowerBounds.sign_degree_communication_lower_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:23:15.860915+00:00
-- url     : https://prove2.me/theorems/1e1bd70a-fd75-4d12-b7e1-37f3c45984a1
-- title:
--   Result 1 — Classical and quantum communication lower bounds from sign degree
-- statement:
--   Fix a positive arity k, a Boolean function f of sign degree d, and alpha in (0,1). The goal is the conjunction of both claims of Result 1:
--
--   $$d\geq2\Longrightarrow R^\rightarrow_{2/3}(f\text{-BHP}_{k,n}^\alpha)=\Omega(n^{1-1/d}),\qquad d\geq3\Longrightarrow Q^\rightarrow_{2/3}(f\text{-BHP}_{k,n}^\alpha)=\Omega(n^{1-2/d}).$$
--
--   Each clause asserts a positive constant a and a threshold n_0, chosen before n and the protocol, such that every admissible n≥n_0 and every protocol succeeding with probability at least 2/3 on every promised input has cost at least a times the indicated power of n. The constants depend only on fixed f (including k,d) and alpha, never on n, the protocol or an input. Classical protocols allow all public/private randomness. Quantum protocols allow arbitrary mixed states, POVMs and public seeds without preshared entanglement.
--
--   The statement is about the operational promise problem, rather than success only under a selected distribution. No symmetry, uniform balance, full support of a witness, small-alpha restriction or bound on local computation is imposed.
--
--   Differences from the source:
--   - encoding: Coordinates in {+1,−1} indexed from 1 → Fin-indexed Bool coordinates with true=−1, and explicit finite averages; reason: The sign map is a bijection and preserves ordered blocks, parities, distributions and all source instances.
--   - encoding: Positive source parameters with alpha n/k an integer → A positive integer m and Layout with k*m=alpha*n; reason: This is the same admissibility condition without truncating division; irrational alpha retains the source admissibility quantifier.
--   - encoding: The least degree of a real sign-representing polynomial → MvPolynomial total degree minimized in WithTop Nat; reason: Polynomial interpolation makes the defining set nonempty and the minimum finite; no source function is excluded.
--   - encoding: Communication complexity is Omega of the stated power → A positive constant and threshold followed by a bound on every successful protocol cost; reason: This is exactly the operational meaning of the complexity lower bound; full-input transmission supplies a finite successful protocol, and both clauses and powers are preserved.
--   - encoding: Bounded error one-way communication → Success at least 2/3 on every promised input in the general protocol types; reason: The standard fixed bounded-error convention makes the adversarial-input quantifiers and randomization explicit.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), pp. 3–4, Result 1.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_SignDegree
import Definitions.Def_BooleanHiddenPartition_LowerBounds_Posteriors

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Result 1, pp.3–4, both clauses for the operational promise problem. -/
theorem sign_degree_communication_lower_bounds :
    (∀ (k : ℕ), 0 < k → ∀ (f : Cube k → Bool) (d : ℕ),
      signDegree f = (d : WithTop ℕ) → 2 ≤ d →
      ∀ α : ℝ, 0 < α → α < 1 →
      ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ, ∀ (n m c : ℕ), n₀ ≤ n →
        ∀ (L : Layout k n m α) (P : ClassicalProtocol (Cube n) (BobInput n m) c),
        ClassicalSolves L f P → a * (n : ℝ) ^ (1 - 1 / (d : ℝ)) ≤ (c : ℝ)) ∧
    (∀ (k : ℕ), 0 < k → ∀ (f : Cube k → Bool) (d : ℕ),
      signDegree f = (d : WithTop ℕ) → 3 ≤ d →
      ∀ α : ℝ, 0 < α → α < 1 →
      ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ, ∀ (n m c : ℕ), n₀ ≤ n →
        ∀ (L : Layout k n m α) (Ω : Type) [MeasurableSpace Ω]
          (P : QuantumProtocol (Cube n) (BobInput n m) Ω c),
        QuantumSolves L f P → a * (n : ℝ) ^ (1 - 2 / (d : ℝ)) ≤ (c : ℝ)) := by sorry

end

end BooleanHiddenPartition.LowerBounds
