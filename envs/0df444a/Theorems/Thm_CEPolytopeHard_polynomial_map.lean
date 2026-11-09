-- Prove2me | Theorems.Thm_CEPolytopeHard_polynomial_map
-- name    : CEPolytopeHard.polynomial_map
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:09.551005+00:00
-- url     : https://prove2.me/theorems/0dff70e5-908b-4b9d-a1bc-01af14c5bb4b
-- title:
--   Proof of Theorem 4(i), "A polynomial map" — $f$ is $3\lambda$-Lipschitz and its $\tau/(4d)$-fixed points satisfy every gate
-- statement:
--   Let $C$ be a well-formed generalized circuit with fan-out two and $d$ nodes, $0 < \tau < 1/4$, $\lambda = \max\{1, 1/(2\tau)\}$, and $p \ge (4\lambda/\tau)^2$ an integer. Let $f$ be the circuit's polynomial map. Then
--
--   1. $f$ maps $[0,1]^d$ into itself;
--   2. on $[0,1]^d$, every coordinate is within $\tau/4$ of its gate map: $|f_i(x) - h_i(x_{a_i}, x_{b_i})| \le \tau/4$;
--   3. in the normalized norm, $\|f(x) - f(y)\|_2 \le \sqrt6\,\lambda\,\|x - y\|_2$ on $[0,1]^d$, and $\sqrt 6\lambda \le 3\lambda$, so $f$ is $3\lambda$-Lipschitz;
--   4. if $x \in [0,1]^d$ and $\|f(x) - x\|_2 \le \delta = \tau/(4d)$, then every coordinate residual satisfies $|f_i(x) - x_i| \le \tau/4$ and $x$ satisfies every gate of $C$ at tolerance $\tau$.
--
--   Hence finding a $\tau/(4d)$-fixed point of $f$ is as hard as satisfying the circuit.
--
--   Differences from the source:
--   - reading: "for a constant λ ≥ 1" (unnamed) → λ = lam τ = max{1, 1/(2τ)}; reason: the least constant ≥ 1 that is a Lipschitz constant of every Section 2.5 gate map
--   - reading: the circuit of [71], whose gate maps on p.20 include OR, AND, NOT; "every input appears at most three times" → any well-formed fan-out-two circuit of the Section 2.5 class (no Boolean gates); reason: Section 2.5 has no Boolean gate type (see the [71] item); fan-out two gives at most two occurrences, within the paper's bound of three
--   - encoding: "Euclidean operator norm of f is at most √6λ" → the Lipschitz bound ‖f(x) − f(y)‖₂ ≤ √6λ‖x − y‖₂ on [0, 1]^d (normalized norm); reason: f is nonlinear; the operator-norm bound is used as this Lipschitz bound, which is homogeneous in the normalization
--   - encoding: d ≥ 1 nodes (implicit) → no assumption on d; reason: for d = 0 every clause is trivially true
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), proof of Theorem 4(i), "A polynomial map", p.20

import Mathlib
import Definitions.Def_CEPolytopeHard_GCircuit
import Definitions.Def_CEPolytopeHard_gateMap
import Definitions.Def_CEPolytopeHard_circuitMap
import Definitions.Def_CEPolytopeHard_nnorm

set_option autoImplicit false

namespace CEPolytopeHard

/-- **The polynomial map of a generalized circuit** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, proof of Theorem 4(i), "A polynomial
map", p.20: "In what follows, we fix an integer p ≥ (4λ/τ)². By Claim 4.1, the approximation
error is at most τ/4. Because every input appears at most three times, it follows that the
Euclidean operator norm of f is at most √6λ ≤ 3λ, giving a Lipschitz bound L = 3λ for f in the
normalized norm as well. We now set δ = τ/(4d). If ∥f(x) − x∥₂ ≤ δ, each coordinate residual is
at most √d δ ≤ τ/4. Accounting for the approximation error, this satisfies every original gate at
tolerance τ").

Let `C` be a well-formed generalized circuit with fan-out two and `d` nodes, `0 < τ < 1/4`,
`λ = max{1, 1/(2τ)}`, and `p ≥ (4λ/τ)²` an integer; let `f` be the circuit's polynomial map. Then
1. `f` maps `[0, 1]^d` into itself;
2. on `[0, 1]^d` every coordinate `f_i` is within `τ/4` of the gate map `h_i` at the inputs;
3. `‖f(x) − f(y)‖₂ ≤ √6 λ‖x − y‖₂` on `[0, 1]^d` (normalized norm), and `√6 λ ≤ 3λ`, so `f` is
   `3λ`-Lipschitz;
4. if `x ∈ [0, 1]^d` and `‖f(x) − x‖₂ ≤ τ/(4d)`, then every coordinate residual is at most `τ/4`
   and every gate is satisfied by `x` at tolerance `τ`.

**Formalization Note** The gate maps are `gateMap` and `λ` is `lam τ`. For `d = 0` every clause
is trivial. -/
theorem polynomial_map (C : GCircuit) (hwf : C.WellFormed) (hfo : C.FanOutTwo) (τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1 / 4) (p : ℕ) (hp : (4 * lam τ / τ) ^ 2 ≤ (p : ℝ)) :
    (∀ x ∈ Set.Icc (0 : Fin C.d → ℝ) 1, circuitMap τ p C x ∈ Set.Icc (0 : Fin C.d → ℝ) 1) ∧
    (∀ x ∈ Set.Icc (0 : Fin C.d → ℝ) 1, ∀ i : Fin C.d,
      |circuitMap τ p C x i - gateMap τ (C.gates.get i) (C.valO x (C.gates.get i).argA)
        (C.valO x (C.gates.get i).argB)| ≤ τ / 4) ∧
    (∀ x ∈ Set.Icc (0 : Fin C.d → ℝ) 1, ∀ y ∈ Set.Icc (0 : Fin C.d → ℝ) 1,
      nnorm (circuitMap τ p C x - circuitMap τ p C y) ≤ Real.sqrt 6 * lam τ * nnorm (x - y)) ∧
    Real.sqrt 6 * lam τ ≤ 3 * lam τ ∧
    (∀ x ∈ Set.Icc (0 : Fin C.d → ℝ) 1, ∀ y ∈ Set.Icc (0 : Fin C.d → ℝ) 1,
      nnorm (circuitMap τ p C x - circuitMap τ p C y) ≤ 3 * lam τ * nnorm (x - y)) ∧
    (∀ x ∈ Set.Icc (0 : Fin C.d → ℝ) 1, nnorm (circuitMap τ p C x - x) ≤ τ / (4 * C.d) →
      (∀ i, |circuitMap τ p C x i - x i| ≤ τ / 4) ∧ ∀ i, GateSat τ C x i) := by sorry

end CEPolytopeHard
