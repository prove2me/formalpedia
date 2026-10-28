-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_failure_accumulation
-- name    : EntanglingOps.BinaryPhase.failure_accumulation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:24.592989+00:00
-- url     : https://prove2.me/theorems/5ad85d51-c046-4a47-aa7b-978ad491a8ad
-- title:
--   p. 3, failure accumulation — after k failed steps U(−α_N)^{2^k−1} has been applied; U(−α_N)^{2^N−1} = −U(α_N)
-- statement:
--   Let $N\ge1$ and $\alpha_N=\pi/2^N$, and run the protocol of p. 3: step $k$ uses the resource $|\psi_{2^{k-1}\alpha_N}\rangle$, and a step fails when its outcomes satisfy $i_1\ne j_1$. Then:
--
--   1. for every $k\le N$, every sequence of $k$ failing outcomes of steps $1,\dots,k$ has applied
--   $$c\;U(-\alpha_N)^{2^k-1}$$
--   to the input, with $c\in\mathbb C$, $|c|^2=(1/16)^k$;
--   2. $$U(-\alpha_N)^{2^N-1}=-U(\alpha_N);$$
--   3. 8 of the 16 equally probable outcomes of a step succeed (so each step succeeds with probability $1/2$).
--
--   Item 2 is why the procedure ends after step $N$: even if every step fails, the gate applied is $U(\alpha_N)$ up to a global phase.
--
--   Differences from the source:
--   - reading: Bell basis |Ψ_{i1,i2}⟩ = 𝟙 ⊗ σ_{i1,i2}|Ψ⟩ with |Ψ⟩ not defined → |Ψ⟩ := |Φ⟩ of Eq. (5) at d = 2, i.e. |Φ⁺⟩ (bellVec); reason: the only reading under which the page's rule (i)/(ii) holds: with |Ψ⁺⟩ all 16 outcomes violate it, with |Φ⟩ all 16 satisfy it
--   - encoding: 'with a probability 1/2 we will succeed' → the number of succeeding outcomes (i₁ = j₁) is 8 of the 16; reason: each outcome has probability 1/16 (step-outcome rule), so this is the probability 1/2
--   - encoding: sequential measurements and corrections acting on states → each outcome history is a (non-normalized) Kraus operator from A3B3 to A1B1; outcome probabilities are Re Tr(K ρ K†); reason: the normalized output of a branch is KρK†/Tr(KρK†), so a branch applies U exactly when K is a scalar multiple of U; same instances
--   - encoding: labels (i1,i2) ∈ {1,2}², steps k = 1, …, N → 0-based labels in Fin 2 × Fin 2 and 0-based list positions (the paper's step k is position k − 1, with resource ψ_{2^{k−1}α_N}); reason: Lean indexing convention; same objects
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 3, protocol paragraph ('With a probability 1/2 we will succeed … so that the procedure ends')

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

/-- p. 3, failure accumulation: for `N ≥ 1` and `k ≤ N`, every history of `k` failing steps
(the 0-based step `s` using `|ψ_{2^s α_N}⟩`) has applied `c · U(−α_N)^{2^k − 1}` with
`|c|² = (1/16)^k`; `U(−α_N)^{2^N − 1} = −U(α_N)`; and 8 of the 16 outcomes of a step succeed. -/
theorem failure_accumulation (N : ℕ) (hN : 1 ≤ N) :
    (∀ k ≤ N, ∀ l ∈ failing k, ∃ c : ℂ, Complex.normSq c = (1 / 16 : ℝ) ^ k ∧
        branchKraus N l = c • gate (-alphaN N) ^ (2 ^ k - 1)) ∧
    gate (-alphaN N) ^ (2 ^ N - 1) = -gate (alphaN N) ∧
    (Finset.univ.filter succeeds).card = 8 := by sorry

end EntanglingOps.BinaryPhase
