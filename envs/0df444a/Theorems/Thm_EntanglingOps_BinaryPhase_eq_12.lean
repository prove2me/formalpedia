-- Prove2me | Theorems.Thm_EntanglingOps_BinaryPhase_eq_12
-- name    : EntanglingOps.BinaryPhase.eq_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:28.379868+00:00
-- url     : https://prove2.me/theorems/e3c1dab0-4dc0-489a-86c6-6c7de28049af
-- title:
--   Eq. (12), p. 3 — step k is performed with probability (1/2)^{k−1}; Ē[U(α_N)] = Σ_k (1/2)^{k−1} E(ψ_{α_{N−k+1}}) = α_N f_N
-- statement:
--   Let $N\ge1$. For every density matrix $\rho$ on the input systems $A_3B_3$:
--
--   1. step $k$ of the protocol is performed with probability $p_k=(1/2)^{k-1}$, for $1\le k\le N$;
--   2. the average entanglement consumed, $\bar E[U(\alpha_N)]=\sum_{k=1}^Np_k\,E(\psi_{2^{k-1}\alpha_N})$, equals
--   $$\bar E[U(\alpha_N)]=\sum_{k=1}^N\Big(\frac12\Big)^{k-1}E(\psi_{\alpha_{N-k+1}});$$
--   3. the average classical communication in each direction, one bit for each performed step $k\le N-1$, is
--   $$\sum_{k=1}^{N-1}p_k=2-\Big(\frac12\Big)^{N-2}\ \text{bits}.$$
--
--   Moreover
--   $$\sum_{k=1}^N\Big(\frac12\Big)^{k-1}E(\psi_{\alpha_{N-k+1}})=\alpha_Nf_N,\qquad f_N=\frac1\pi\sum_{k=1}^N2^kE(\psi_{\alpha_k}).$$
--
--   This is the cost of the protocol: entanglement linear in the phase $\alpha_N$, and about two bits of communication each way.
--
--   Differences from the source:
--   - reading: Bell basis |Ψ_{i1,i2}⟩ = 𝟙 ⊗ σ_{i1,i2}|Ψ⟩ with |Ψ⟩ not defined → |Ψ⟩ := |Φ⟩ of Eq. (5) at d = 2, i.e. |Φ⁺⟩ (bellVec); reason: the only reading under which the page's rule (i)/(ii) holds: with |Ψ⁺⟩ all 16 outcomes violate it, with |Φ⟩ all 16 satisfy it
--   - reading: footnote [20]: the local step U(π/2) is 'step (N − 1)' and '(N − 2) steps' are performed → the local step is step N (it uses ψ_{2^{N−1}α_N} = ψ_{π/2}); communication counts steps 1, …, N − 1: avgComm = Σ_{k=1}^{N−1} P(step k); reason: step k uses ψ_{2^{k−1}α_N}, so U(π/2) is step N, and Σ_{k=1}^{N−1}(1/2)^{k−1} is exactly the printed 2 − (1/2)^{N−2}
--   - encoding: Ē[U(α_N)] and 'p_k gives the probability that the k-th step has to be performed' → avgEnt := Σ_k reachProb · E(resource of step k) with reachProb computed from the Kraus operators; (1/2)^{k−1} is a conclusion; reason: the definition is the paper's description of Ē; the probabilities are not set by hand
--   - encoding: (1/2)^{N−2} → real zpow (1/2 : ℝ)^((N : ℤ) − 2); reason: at N = 1 the exponent is −1 and both sides are 0; natural-number subtraction would truncate
--   - encoding: labels (i1,i2) ∈ {1,2}², steps k = 1, …, N → 0-based labels in Fin 2 × Fin 2 and 0-based list positions (the paper's step k is position k − 1, with resource ψ_{2^{k−1}α_N}); reason: Lean indexing convention; same objects
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 3, Eq. (12), the sentence 'In (12), the weight factor …' and the communication sentence; footnote [20], p. 4

import Mathlib
import Definitions.Def_EntanglingOps_BinaryPhase_Model

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped ComplexOrder

/-- Eq. (12), p. 3, with the probability sentence and the communication sentence: for `N ≥ 1` and
every density matrix `ρ` on `A₃B₃`, the paper's step `k` is performed with probability
`(1/2)^{k−1}` (`1 ≤ k ≤ N`), the average entanglement is
`Ē[U(α_N)] = ∑_{k=1}^N (1/2)^{k−1} E(ψ_{α_{N−k+1}})`, and the average communication in each
direction (steps `1, …, N − 1`) is `2 − (1/2)^{N−2}` bits; and
`∑_{k=1}^N (1/2)^{k−1} E(ψ_{α_{N−k+1}}) = α_N f_N`. -/
theorem eq_12 (N : ℕ) (hN : 1 ≤ N) :
    (∀ ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ, ρ.PosSemidef → ρ.trace = 1 →
      (∀ k ∈ Finset.Icc 1 N, reachProb N ρ k = (1 / 2 : ℝ) ^ (k - 1)) ∧
      avgEnt N ρ = ∑ k ∈ Finset.Icc 1 N,
        (1 / 2 : ℝ) ^ (k - 1) * entEntropy (resource (alphaN (N - k + 1))) ∧
      avgComm N ρ = 2 - (1 / 2 : ℝ) ^ ((N : ℤ) - 2)) ∧
    ∑ k ∈ Finset.Icc 1 N, (1 / 2 : ℝ) ^ (k - 1) * entEntropy (resource (alphaN (N - k + 1))) =
      alphaN N * fN N := by sorry

end EntanglingOps.BinaryPhase
