-- Prove2me | Theorems.Thm_DeFinettiSDP_NoSymm_theorem_2_5
-- name    : DeFinettiSDP.NoSymm.theorem_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:46:42.694982+00:00
-- url     : https://prove2.me/theorems/4ec16c14-686b-4a63-a12a-1d9a847bea07
-- title:
--   Theorem 2.5, p. 9 — random subsystems are close to product in expectation
-- statement:
--   Let $\rho$ be an arbitrary state on $n=k+r$ copies of a $d_B$-dimensional system, with $k\ge1$. Choose the ordered $k$ retained systems and the ordered $r$ other systems by a uniform random permutation. Use a state-two-design measurement on the other systems. There is an $m\in\{0,\ldots,r\}$ such that, after measuring the first $m$ of them and conditioning on their outcomes,
--
--   $$
--   \mathbb E\left\|\rho_{\vec i\mid z}-\bigotimes_{s=1}^k\rho_{i_s\mid z}\right\|_1
--   \le k d_B^2(d_B+1)\sqrt{\frac{(2\ln2)(k-1)\log_2 d_B}{r+1}}
--   \le \frac{3k^{3/2}d_B^3\log_2 d_B}{\sqrt{r+1}}.
--   $$
--
--   This is the paper's explicit polynomial-dimension de Finetti estimate without a symmetry hypothesis. The expectation is over the random ordered systems and the measurement outcomes, whereas $m$ is selected outside that expectation.
--
--   **Formalization Note** The theorem's unspecified measurement $M_B$ is fixed here to the state-two-design measurement of Lemma D.1; the proof on p. 10 explicitly directs replacing $f(B\mid\cdot)$ by $d_B^2(d_B+1)$ for this choice. The Lean statement assumes such a design with at least one outcome, and $k\ge1$; it writes $n=k+r$. Logarithms are base two except for $\ln2$.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, Theorem 2.5, p. 9; measurement choice in proof, p. 10

import Mathlib
import Definitions.Def_DeFinettiSDP_NoSymm_Random

namespace DeFinettiSDP.NoSymm

/-- Theorem 2.5, p. 9, with the two-design measurement of Lemma D.1, as the
proof explicitly permits on p. 10. The page's `n` is `k+r`, so its `n-k+1` is
`r+1`; `k ≥ 1` ensures at least one kept system. Logarithms in the source are
base two except for the explicit natural logarithm `ln 2`. -/
theorem theorem_2_5 {dB t : ℕ} (k r : ℕ) (hk : 1 ≤ k)
    (ρ : Matrix (Fin (k + r) → Fin dB) (Fin (k + r) → Fin dB) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ)
    (P : Fin t → Matrix (Fin dB) (Fin dB) ℂ)
    (ht : 0 < t) (hP : DeFinettiSDP.Hierarchy.IsStateTwoDesign P) :
    ∃ m : ℕ, m ≤ r ∧
      rsError k r ρ (DeFinettiSDP.Hierarchy.designMeas P) m ≤
        (k : ℝ) * ((dB : ℝ) ^ 2 * ((dB : ℝ) + 1)) *
          Real.sqrt (2 * Real.log 2 * ((k : ℝ) - 1) *
            Real.logb 2 (dB : ℝ) / ((r : ℝ) + 1)) ∧
      (k : ℝ) * ((dB : ℝ) ^ 2 * ((dB : ℝ) + 1)) *
          Real.sqrt (2 * Real.log 2 * ((k : ℝ) - 1) *
            Real.logb 2 (dB : ℝ) / ((r : ℝ) + 1)) ≤
        3 * (k : ℝ) ^ ((3 : ℝ) / 2) * (dB : ℝ) ^ 3 *
          Real.logb 2 (dB : ℝ) / Real.sqrt ((r : ℝ) + 1) := by sorry

end DeFinettiSDP.NoSymm
