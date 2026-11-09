-- Prove2me | Theorems.Thm_CEPolytopeHard_pcp_decoding
-- name    : CEPolytopeHard.pcp_decoding
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:16.602636+00:00
-- url     : https://prove2.me/theorems/89f3a7e2-2745-4386-8a6b-3c980eb0ed52
-- title:
--   Proof of Theorem 4(ii) — a $\delta$-fixed point of $f$ satisfies $(1-\gamma)d$ gates
-- statement:
--   Let $C$ be a well-formed generalized circuit with fan-out two and $d$ nodes, $0 < \tau < 1/4$, $0 < \gamma < 1$, $\lambda = \max\{1, 1/(2\tau)\}$, $p \ge (4\lambda/\tau)^2$ an integer, $f$ the circuit's polynomial map, and $\delta > 0$ with $\delta^2 \le \gamma\tau^2/64$. For every $x \in [0,1]^d$ with $\|f(x) - x\|_2 \le \delta$ (normalized norm):
--
--   1. $\displaystyle \frac1d\,\big|\{i : |f_i(x) - x_i| > \tau/4\}\big| \le \frac{16\delta^2}{\tau^2} \le \frac\gamma4$;
--   2. every $i$ with $|f_i(x) - x_i| \le \tau/4$ has $|h_i - x_i| \le \tau/2$ (the gate map at the inputs of gate $i$), and gate $i$ is satisfied at tolerance $\tau$;
--   3. $x$ satisfies at least $(1-\gamma)d$ gates at tolerance $\tau$.
--
--   Under Assumption 2.2 this makes the fixed-point problem hard already at constant accuracy $\delta$, which gives the polynomial accuracy of Theorem 4(ii).
--
--   Differences from the source:
--   - reading: "for a constant λ ≥ 1" (unnamed) → λ = lam τ = max{1, 1/(2τ)}; reason: the least constant ≥ 1 that is a Lipschitz constant of every Section 2.5 gate map
--   - encoding: |{i : …}|; "can be decoded in polynomial time" → Set.ncard; the decoding is part of the reduction of Theorem 4(ii), not of this item; reason: Lean representation; the polynomial-time claim belongs to the goal's proof
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), proof of Theorem 4(ii), p.25

import Mathlib
import Definitions.Def_CEPolytopeHard_GCircuit
import Definitions.Def_CEPolytopeHard_gateMap
import Definitions.Def_CEPolytopeHard_circuitMap
import Definitions.Def_CEPolytopeHard_nnorm

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Decoding a fixed point under PCP-for-PPAD** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, proof of Theorem 4(ii), p.25: "We use again
the Bernstein approximation with p ≥ (4λ/τ)², and choose a parameter δ such that δ² ≤ γτ²/64. If
∥f(x) − x∥₂ ≤ δ, then (1/d)|{i : |f_i(x) − x_i| > τ/4}| ≤ 16δ²/τ² ≤ γ/4. Every other coordinate
satisfies |h_i(x) − x_i| ≤ τ/2 by the Bernstein error bound, so the corresponding gate is satisfied
at tolerance τ. The assignment therefore satisfies at least (1 − γ)d gates").

Let `C` be a well-formed fan-out-two generalized circuit with `d` nodes, `0 < τ < 1/4`,
`0 < γ < 1`, `λ = max{1, 1/(2τ)}`, `p ≥ (4λ/τ)²` an integer, `f` the circuit's polynomial map, and
`δ > 0` with `δ² ≤ γτ²/64`. For every `x ∈ [0, 1]^d` with `‖f(x) − x‖₂ ≤ δ` (normalized norm):
1. `(1/d)|{i : |f_i(x) − x_i| > τ/4}| ≤ 16δ²/τ² ≤ γ/4`;
2. every `i` with `|f_i(x) − x_i| ≤ τ/4` has `|h_i − x_i| ≤ τ/2` (at the inputs of gate `i`) and
   its gate is satisfied at tolerance `τ`;
3. at least `(1 − γ)d` gates are satisfied by `x` at tolerance `τ`.

**Formalization Note** `h_i` is `gateMap τ` of gate `i`; cardinalities are `Set.ncard`. -/
theorem pcp_decoding (C : GCircuit) (hwf : C.WellFormed) (hfo : C.FanOutTwo) (τ γ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1 / 4) (hγ0 : 0 < γ) (hγ1 : γ < 1) (p : ℕ)
    (hp : (4 * lam τ / τ) ^ 2 ≤ (p : ℝ)) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ^ 2 ≤ γ * τ ^ 2 / 64)
    (x : Fin C.d → ℝ) (hx : x ∈ Set.Icc (0 : Fin C.d → ℝ) 1)
    (hfix : nnorm (circuitMap τ p C x - x) ≤ δ) :
    1 / (C.d : ℝ) * ({i : Fin C.d | τ / 4 < |circuitMap τ p C x i - x i|}.ncard : ℝ) ≤
      16 * δ ^ 2 / τ ^ 2 ∧
    16 * δ ^ 2 / τ ^ 2 ≤ γ / 4 ∧
    (∀ i : Fin C.d, |circuitMap τ p C x i - x i| ≤ τ / 4 →
      |gateMap τ (C.gates.get i) (C.valO x (C.gates.get i).argA) (C.valO x (C.gates.get i).argB) -
        x i| ≤ τ / 2 ∧ GateSat τ C x i) ∧
    (1 - γ) * (C.d : ℝ) ≤ ({i : Fin C.d | GateSat τ C x i}.ncard : ℝ) := by sorry

end CEPolytopeHard
