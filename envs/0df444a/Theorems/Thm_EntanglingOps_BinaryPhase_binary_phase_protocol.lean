-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_binary_phase_protocol
-- name    : EntanglingOps.BinaryPhase.binary_phase_protocol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:32.61256+00:00
-- url     : https://prove2.me/theorems/91b34797-c373-42a7-b495-1bbb099f0f65
-- title:
--   p. 3, protocol and Eqs. (12)–(13) (corrected: 5.97931 < f_∞ < 5.97932) — U(π/2^N) with unit probability, P(step k) = 2^{1−k}, Ē = α_N f_N < α_N f_∞, 2 − 2^{2−N} cbits
-- statement:
--   Let $N\ge1$, $\alpha_N=\pi/2^N$ and $U(\alpha)=e^{-i\alpha\,\sigma_x\otimes\sigma_x}$. The protocol of p. 3 implements $U(\alpha_N)$ on $A_3B_3$, with output on $A_1B_1$: step $k$ ($k=1,\dots,N$) consumes a fresh pair of resource states $|\psi_{2^{k-1}\alpha_N}\rangle$ (Eq. (10)) on $A_1A_2$ and $B_1B_2$, measures $A_2A_3$ and $B_2B_3$ in the Bell basis and applies Pauli corrections on $A_1$, $B_1$; it stops at the first success ($i_1=j_1$) or after step $N$. Then:
--
--   1. **Every branch is correct.** For every terminal history of outcomes, the history's operator is $c\,U(\alpha_N)$ for some $c\in\mathbb C$.
--   2. **Unit probability.** The operators $K_l$ of the terminal histories satisfy $\sum_lK_l^\dagger K_l=\mathbb 1$.
--   3. **Probabilities, entanglement and communication.** For every density matrix $\rho$ on $A_3B_3$: step $k$ is performed with probability $(1/2)^{k-1}$ ($1\le k\le N$); the average entanglement consumed is
--   $$\bar E[U(\alpha_N)]=\alpha_Nf_N,\qquad f_N=\frac1\pi\sum_{k=1}^N2^kE(\psi_{\alpha_k});$$
--   and the average classical communication in each direction is $2-(1/2)^{N-2}$ bits.
--   4. **The constant.** $f_N<f_\infty=\frac1\pi\sum_{k=1}^\infty2^kE(\psi_{\alpha_k})$, the series converges, and
--   $$5.97931<f_\infty<5.97932.$$
--
--   By 1 and 2, every input $\rho$ is mapped to $U(\alpha_N)\rho\,U(\alpha_N)^\dagger$ with probability one; by 3 and 4, this costs less than $5.97932\,\alpha_N$ ebits on average. The paper's headline: gates with small phase can be implemented nonlocally with far less than one ebit.
--
--   Differences from the source:
--   - correction: f_∞ = 5.97932 → 5.97931 < f_∞ < 5.97932; reason: f_∞ = 5.9793137464654… (40-digit evaluation of (1/π) Σ 2^k h(cos²(π/2^k))), which is 5.97931 to the printed precision
--   - reading: Bell basis |Ψ_{i1,i2}⟩ = 𝟙 ⊗ σ_{i1,i2}|Ψ⟩ with |Ψ⟩ not defined → |Ψ⟩ := |Φ⟩ of Eq. (5) at d = 2, i.e. |Φ⁺⟩ (bellVec); reason: the only reading under which the page's rule (i)/(ii) holds: with |Ψ⁺⟩ all 16 outcomes violate it, with |Φ⟩ all 16 satisfy it
--   - reading: footnote [20]: the local step U(π/2) is 'step (N − 1)', '(N − 2) steps' are performed → the local step is step N; communication = Σ_{k=1}^{N−1} P(step k); reason: step k uses ψ_{2^{k−1}α_N}, so U(π/2) is step N; Σ_{k=1}^{N−1}(1/2)^{k−1} is exactly the printed 2 − (1/2)^{N−2}
--   - encoding: 'with probability one we apply the desired gate' → clause 1 (each terminal branch operator is c·U(α_N)) and clause 2 (Σ K†K = 𝟙); reason: each branch maps ρ to UρU† after normalization and the branch weights sum to Tr ρ on every input; same claim
--   - encoding: sequential measurements and corrections acting on states → each outcome history is a (non-normalized) Kraus operator from A3B3 to A1B1; outcome probabilities are Re Tr(K ρ K†); reason: the normalized output of a branch is KρK†/Tr(KρK†), so a branch applies U exactly when K is a scalar multiple of U; same instances
--   - encoding: labels (i1,i2) ∈ {1,2}², steps k = 1, …, N → 0-based labels in Fin 2 × Fin 2 and 0-based list positions (the paper's step k is position k − 1, with resource ψ_{2^{k−1}α_N}); reason: Lean indexing convention; same objects
--   - encoding: (1/2)^{N−2} → real zpow (1/2 : ℝ)^((N : ℤ) − 2); reason: at N = 1 the exponent is −1 and both sides are 0
--   - encoding: f_∞ as an infinite sum → tsum with summability asserted; reason: Lean's tsum is 0 on a non-summable series
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 3, protocol paragraph and Eqs. (12)–(13) with the communication sentence; footnote [20], p. 4

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped ComplexOrder

/-- p. 3, the protocol with Eqs. (12)–(13) and the communication sentence; footnote [20], p. 4.
For `N ≥ 1`: every terminal history of the `N`-step protocol applies `U(α_N)` up to a scalar;
the terminal Kraus operators sum to the identity (`∑ K†K = 𝟙`, unit probability); on every
density matrix `ρ` the paper's step `k` is performed with probability `(1/2)^{k−1}`, the average
entanglement is `Ē[U(α_N)] = α_N f_N` and the average communication in each direction is
`2 − (1/2)^{N−2}` bits; `f_N < f_∞`, the series defining `f_∞` converges, and
`5.97931 < f_∞ < 5.97932` (corrected from the printed `f_∞ = 5.97932`). -/
theorem binary_phase_protocol (N : ℕ) (hN : 1 ≤ N) :
    (∀ l ∈ terminal N, ∃ c : ℂ, branchKraus N l = c • gate (alphaN N)) ∧
    ∑ l ∈ terminal N, (branchKraus N l)ᴴ * branchKraus N l = 1 ∧
    (∀ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, ρ.PosSemidef → ρ.trace = 1 →
      (∀ k ∈ Finset.Icc 1 N, reachProb N ρ k = (1 / 2 : ℝ) ^ (k - 1)) ∧
      avgEnt N ρ = alphaN N * fN N ∧
      avgComm N ρ = 2 - (1 / 2 : ℝ) ^ ((N : ℤ) - 2)) ∧
    fN N < fInf ∧
    Summable (fun k : ℕ => (2 : ℝ) ^ (k + 1) * entEntropy (resource (alphaN (k + 1)))) ∧
    (5.97931 : ℝ) < fInf ∧ fInf < 5.97932 := by sorry

end EntanglingOps.BinaryPhase
