-- Prove2me | Theorems.Thm_DQI_Semicircle_theorem_4_1
-- name    : DQI.Semicircle.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:27.909963+00:00
-- url     : https://prove2.me/theorems/2f3646ad-7ea3-4aaf-b0a7-4c0c6f1d6408
-- title:
--   Theorem 4.1 — if 2ℓ+1 < d⊥, the optimal degree-ℓ DQI state has ⟨s⟩/m → (√(μ(1−r/p)) + √((r/p)(1−μ)))² for r/p ≤ 1−μ, and → 1 otherwise
-- statement:
--   Fix a prime $p$ and an integer $r\in\{1,\dots,p-1\}$, and let $\mu\ge0$. Consider a sequence of max-LINSAT instances $(B_j,F^{(j)})$, $B_j\in\mathbb F_p^{m_j\times n_j}$ with $m_j>n_j$, in which every constraint set has $|F^{(j)}_i|=r$, together with degrees $\ell_j$ such that $\ell_j/m_j\to\mu$, $m_j\to\infty$, and $2\ell_j+1<d^\perp_j$, where $d^\perp_j$ is the minimum Hamming weight of a nonzero codeword of $C_j^\perp=\{\mathbf d\in\mathbb F_p^{m_j}:B_j^T\mathbf d=0\}$.
--
--   For each $j$ let $\langle s\rangle_{\rm opt}$ be the largest expected number of satisfied constraints obtainable by measuring a DQI state $|P(f)\rangle=\sum_{\mathbf x}P(f(\mathbf x))|\mathbf x\rangle$ in the computational basis, over polynomials $P$ of degree at most $\ell_j$ with $\langle P(f)|P(f)\rangle=1$. Then, with $\rho=r/p$,
--   $$\lim_{j\to\infty}\frac{\langle s\rangle_{\rm opt}}{m_j}=\begin{cases}\Big(\sqrt{\mu(1-\rho)}+\sqrt{\rho(1-\mu)}\Big)^2, & \rho\le1-\mu,\\[2pt] 1, & \text{otherwise.}\end{cases}$$
--
--   This is the semicircle law of decoded quantum interferometry: as long as the dual code can in principle correct $\ell$ errors, the best DQI state of degree $\ell$ satisfies an explicit fraction of the constraints that depends only on $r/p$ and $\ell/m$.
--
--   **Formalization Note** "In the limit $m\to\infty$ with $\ell/m$ fixed" is encoded as an arbitrary sequence of instances with $m_j\to\infty$ and $\ell_j/m_j\to\mu$; this includes irrational $\mu$. The parameters $p$ and $r$ are fixed along the sequence, as in the statement. $m>n$ is the paper's standing assumption. Polynomials are real with `natDegree ≤ ℓ`; the optimum over complex polynomials is the same. The distance hypothesis quantifies over nonzero codewords only.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 11, Theorem 4.1, (9); proof pp. 25–34, (139)

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace DQI.Semicircle

/-- Theorem 4.1, p. 11 (with (139), p. 34). Fixed prime `p` and `r ∈ {1, …, p−1}`; a sequence of
instances `j ↦ (B_j, F_j)` with `m_j → ∞`, `ℓ_j/m_j → μ` and `2ℓ_j + 1 < d^⊥`. -/
theorem theorem_4_1 (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 1 ≤ r) (hrp : r < p) (μ : ℝ) (hμ : 0 ≤ μ)
    (m n ℓ : ℕ → ℕ) (B : ∀ j, Matrix (Fin (m j)) (Fin (n j)) (ZMod p))
    (F : ∀ j, Fin (m j) → Finset (ZMod p)) (hF : ∀ j i, (F j i).card = r) (hnm : ∀ j, n j < m j)
    (hdist : ∀ j, DistGt (B j) (2 * ℓ j + 1))
    (hratio : Filter.Tendsto (fun j => (ℓ j : ℝ) / (m j : ℝ)) Filter.atTop (nhds μ))
    (hm : Filter.Tendsto m Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun j => optSat (B j) (F j) (ℓ j) / m j) Filter.atTop
      (nhds (semicircle ((r : ℝ) / p) μ)) := by sorry

end DQI.Semicircle
