-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_step_outcome_rule
-- name    : EntanglingOps.BinaryPhase.step_outcome_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:19.492122+00:00
-- url     : https://prove2.me/theorems/de83f586-d041-4177-a7ef-5be7791af234
-- title:
--   p. 3, step-outcome rule — each Bell outcome has probability 1/16; the step applies U(β) if i₁ = j₁ and U(−β) = U(β)† if i₁ ≠ j₁
-- statement:
--   Fix a real $\beta$ and let systems $A_1A_2$ and $B_1B_2$ be in the state $|\psi_\beta\rangle$ of Eq. (10). Measure $A_2A_3$ and $B_2B_3$ in the Bell basis $|\Psi_{i_1,i_2}\rangle=(\mathbb 1\otimes\sigma_{i_1,i_2})|\Phi\rangle$, where $\sigma_{1,1}=\mathbb 1$, $\sigma_{1,2}=\sigma_x$, $\sigma_{2,1}=\sigma_y$, $\sigma_{2,2}=\sigma_z$; on outcome $|\Psi_{i}\rangle$ for $A_2A_3$ apply $\sigma_{i}$ to $A_1$, and on outcome $|\Psi_j\rangle$ for $B_2B_3$ apply $\sigma_j$ to $B_1$. Let $K_\beta(i,j)$ be the resulting operator from $A_3B_3$ to $A_1B_1$. Then:
--
--   1. for all outcomes $i=(i_1,i_2)$, $j=(j_1,j_2)$ there is $c\in\mathbb C$ with $|c|^2=1/16$ and
--   $$K_\beta(i,j)=\begin{cases}c\,U(\beta)&\text{if }i_1=j_1,\\ c\,U(-\beta)&\text{if }i_1\neq j_1;\end{cases}$$
--   2. $U(\beta)^\dagger=U(-\beta)$;
--   3. on every density matrix $\rho$ of $A_3B_3$, each of the 16 outcomes has probability $\operatorname{Re}\operatorname{Tr}(K_\beta(i,j)\,\rho\,K_\beta(i,j)^\dagger)=1/16$.
--
--   So all outcomes are equally probable, and the step applies the gate $U(\beta)$ in 8 of the 16 cases and its inverse in the others. This is the elementary step of the protocol.
--
--   Differences from the source:
--   - generalization: the step with resource ψ_{α_N} → every real β; reason: the protocol's step k uses β = 2^{k−1}α_N; β = α_N is an instance
--   - reading: Bell basis |Ψ_{i1,i2}⟩ = 𝟙 ⊗ σ_{i1,i2}|Ψ⟩ with |Ψ⟩ not defined → |Ψ⟩ := |Φ⟩ of Eq. (5) at d = 2, i.e. |Φ⁺⟩ (bellVec); reason: the only reading under which the page's rule (i)/(ii) holds: with |Ψ⁺⟩ all 16 outcomes violate it, with |Φ⟩ all 16 satisfy it
--   - encoding: 'the resulting operation will be U(α_N)' (resp. U(−α_N)) → the step's Kraus operator equals c·U(±β) with |c|² = 1/16; reason: the post-measurement state is K ρ K†/Tr(K ρ K†) = U ρ U†; the scalar is the outcome's amplitude
--   - encoding: labels (i1,i2) ∈ {1,2}², steps k = 1, …, N → 0-based labels in Fin 2 × Fin 2 and 0-based list positions (the paper's step k is position k − 1, with resource ψ_{2^{k−1}α_N}); reason: Lean indexing convention; same objects
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 3, protocol paragraph ('Note that all outcomes of the measurement are equally probable … (ii) U(α_N)† = U(−α_N) if i1 ≠ j1')

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker ComplexOrder

/-- p. 3, the step-outcome rule: with the resource `|ψ_β⟩`, each of the 16 Bell outcomes
`(i, j)` (Alice's on `A₂A₃`, Bob's on `B₂B₃`), followed by the corrections `σ_i` on `A₁` and
`σ_j` on `B₁`, acts on `A₃B₃ → A₁B₁` as `c · U(β)` if `i₁ = j₁` and `c · U(−β)` if `i₁ ≠ j₁`,
with `|c|² = 1/16`; `U(β)† = U(−β)`; and every outcome has probability `1/16` on every input
density matrix. Stated for every real `β` (the paper's step uses `β = α_N`). -/
theorem step_outcome_rule :
    (∀ (β : ℝ) (i j : Fin 2 × Fin 2), ∃ c : ℂ, Complex.normSq c = 1 / 16 ∧
        stepKraus β i j = c • gate (if i.1 = j.1 then β else -β)) ∧
    (∀ β : ℝ, (gate β)ᴴ = gate (-β)) ∧
    (∀ (β : ℝ) (i j : Fin 2 × Fin 2) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
        ρ.PosSemidef → ρ.trace = 1 →
        (Matrix.trace (stepKraus β i j * ρ * (stepKraus β i j)ᴴ)).re = 1 / 16) := by sorry

end EntanglingOps.BinaryPhase
