-- Prove2me | Theorems.Thm_FRouting_Supplement_theorem_6_3
-- name    : FRouting.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:22:20.59225+00:00
-- url     : https://prove2.me/theorems/effb95c8-b13e-4776-8d55-ecd92cc45410
-- title:
--   Theorem 6.3 — deterministic fidelity estimation for Clifford+T reduced states
-- statement:
--   Let $W_\rho$ and $W_\sigma$ be Clifford+T circuits on $q_\rho$ and $q_\sigma$ qubits, with no input wires, each of size at most $L$ and with at most $t$ magic ($T$) gates, and let $A$ be a common set of $a$ output wires. Put $|\rho\rangle=W_\rho|0^{q_\rho}\rangle$, $|\sigma\rangle=W_\sigma|0^{q_\sigma}\rangle$, $\rho_A=\operatorname{tr}_{E_\rho}|\rho\rangle\langle\rho|$ and $\sigma_A=\operatorname{tr}_{E_\sigma}|\sigma\rangle\langle\sigma|$, where $E$ denotes the other wires. Let $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ be the root fidelity.
--
--   There are a deterministic machine $M$ and a constant $c$ such that, for all such circuits and every $k\ge0$, $M$ on input the descriptions of $W_\rho$, $W_\sigma$ and $k$ in unary halts within
--   $$c\,\bigl(2^{t}+L+q_\rho+q_\sigma+k+2\bigr)^{c}$$
--   steps and outputs a rational $\widetilde F$ with
--   $$\bigl|\widetilde F-F(\rho_A,\sigma_A)\bigr|\le 2^{-k}.$$
--
--   Taking $k=\lceil\log_2(1/\delta)\rceil$ gives accuracy $\delta$ in time $\mathrm{poly}(2^t,L,q_\rho+q_\sigma,\log(1/\delta))$. This is the classical simulation step behind Theorem 1.5: the cost is exponential only in the number of magic gates.
--
--   Differences from the source:
--   - reading: "For every δ ∈ (0, 1) … a deterministic classical algorithm" → one machine for all inputs, with δ = 2^{-k} given by k in unary; reason: the printed order allows one algorithm per δ; the uniform reading is the stronger one and covers every δ ∈ (0,1) by k = ⌈log₂(1/δ)⌉, at cost poly(log(1/δ))
--   - reading: Clifford+T circuits and magic gates (no gate list) → gates {H, S, CNOT, T}, magic count = number of T gates; reason: the standard Clifford+T generating set, with S a free Clifford gate
--   - encoding: poly(2^t, L, q_ρ + q_σ, log(1/δ)) → c·(2^t + L + q_ρ + q_σ + k + 2)^c for one constant c; reason: every polynomial with nonnegative arguments is bounded by such an expression and each such expression is a polynomial
--   - encoding: t magic gates and size ≤ L for each circuit → t and L are the larger magic count and size of W_ρ, W_σ; reason: the smallest t and L satisfying the setup
--   - encoding: the output F̃ → a rational printed in the binary description encRat; reason: the paper fixes no output format
--   - generalization: δ ∈ (0, 1) → also k = 0, i.e. δ = 1; reason: an extra input with an easy requirement; the instances δ ∈ (0,1) are unchanged
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 6.3, p.23 (setup on p.23)

import Definitions.Def_FRouting_Supplement_CTCircuit
import Definitions.Def_FRouting_Supplement_encRat
import Definitions.Def_FRouting_StrMachine
import Definitions.Def_WildeQIT_fidelity

set_option autoImplicit false

namespace FRouting.Supplement

open WildeQIT QAlgorithms.Complexity

/-- **Theorem 6.3 — deterministic fidelity estimation for Clifford+T reduced states.** Renard,
*Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 6.3, p.23:
"For every δ ∈ (0, 1), given W_ρ and W_σ, a deterministic classical algorithm outputs F̃ satisfying
|F̃ − F(ρ_A, σ_A)| ≤ δ. The algorithm runs in deterministic time poly(2ᵗ, L, q_ρ + q_σ, log(1/δ))."
Setup (p.23): Clifford+T circuits `W_ρ, W_σ` of size at most `L` with at most `t` magic gates on `q_ρ`
and `q_σ` qubits, `|ρ⟩ = W_ρ|0^{q_ρ}⟩`, `ρ_A = tr_{E_ρ}|ρ⟩⟨ρ|`, and likewise `σ_A`.

**Formalization Note** One machine `M` for all inputs. The circuits have no input wires, `q_ρ, q_σ`
ancillas, and the same `a` kept wires `A`; `ρ_A, σ_A` are their output states. The accuracy is
`δ = 2^{-k}`, with `k` given in unary, so every `δ ∈ (0, 1)` is covered by `k = ⌈log₂(1/δ)⌉`. `L` and
`t` are the larger size and magic count of the two circuits. `poly(·)` is `c (2ᵗ + L + q_ρ + q_σ + k + 2)ᶜ`,
which every polynomial is bounded by for some `c`. `F` is the root fidelity `‖√ρ√σ‖₁` (Theorem 6.9,
p.25). The output `F̃` is a rational printed as `encRat`. -/
theorem theorem_6_3 :
    ∃ (M : StrMachine) (c : ℕ), ∀ (a : ℕ) (Wρ Wσ : CTCircuit 0 a) (k : ℕ),
      ∃ r : ℚ,
        PrintsInTime M (encCTCircuit Wρ ++ encCTCircuit Wσ ++ encNat k) (encRat r)
          (c * (2 ^ max Wρ.magicCount Wσ.magicCount + max Wρ.size Wσ.size +
            (Wρ.ancillas + Wσ.ancillas) + k + 2) ^ c) ∧
        |(r : ℝ) - rootFidelity Wρ.toCircuit.outputState Wσ.toCircuit.outputState| ≤ (1 / 2 : ℝ) ^ k := by sorry

end FRouting.Supplement
