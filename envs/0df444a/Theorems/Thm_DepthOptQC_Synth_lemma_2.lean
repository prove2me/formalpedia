-- Prove2me | Theorems.Thm_DepthOptQC_Synth_lemma_2
-- name    : DepthOptQC.Synth.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:13:53.635358+00:00
-- url     : https://prove2.me/theorems/2f2a0ae6-b92a-4188-b4ed-cf28971828fc
-- title:
--   Lemma 2 — integer approximation: $n_0+\dots+n_3=2^m$ with $|((n_0-n_1)+i(n_2-n_3))/2^m-\tfrac12e^{i\theta/2}|\le\varepsilon$
-- statement:
--   Fix $\theta\in\mathbb R$ and $\varepsilon\in(0,1)$. For every integer $m\ge\lceil\log_2(2\sqrt2/\varepsilon)\rceil$ there exist nonnegative integers $n_0,n_1,n_2,n_3$ with
--   $$
--   n_0+n_1+n_2+n_3=2^m
--   $$
--   such that
--   $$
--   \left|\frac{(n_0-n_1)+i(n_2-n_3)}{2^m}-\frac12e^{i\theta/2}\right|\le\varepsilon .
--   $$
--
--   The four integers are the sizes of four intervals partitioning the $2^m$ addresses of a uniform superposition; on them the circuit applies $I,-I,-iZ,iZ$, so the resulting block is $\operatorname{diag}(\bar z,z)$ with $z\approx\frac12e^{i\theta/2}$, an approximate block encoding of $\frac12R_z(\theta)$.
--
--   **Formalization Note** The integers are a function $n:\{0,1,2,3\}\to\mathbb N$; $m$ is a natural number compared with the integer ceiling.
--
--   Differences from the source:
--   - encoding: nonnegative integers n₀, n₁, n₂, n₃ and an integer m ≥ ⌈log₂(2√2/ε)⌉ → n : Fin 4 → ℕ and m : ℕ with ⌈log₂(2√2/ε)⌉ ≤ (m : ℤ); reason: same instances: the ceiling is at least 2 on (0,1), so every admissible m is a natural number
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Lemma 2, p.15

import Mathlib

namespace DepthOptQC.Synth

/-- **Lemma 2 (Integer Approximation)** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, Lemma 2, p.15). Fix `θ ∈ ℝ` and `ε ∈ (0, 1)`. For any integer
`m ≥ ⌈log₂(2√2/ε)⌉` there are nonnegative integers `n₀, n₁, n₂, n₃` with
`n₀ + n₁ + n₂ + n₃ = 2^m` (20) and
`|((n₀ − n₁) + i(n₂ − n₃))/2^m − ½ e^{iθ/2}| ≤ ε` (21).

**Formalization Note.** The four integers are `n : Fin 4 → ℕ`; `m` is a natural number, compared with
the integer ceiling `⌈log₂(2√2/ε)⌉` in `ℤ` (that ceiling is at least `2` on `(0, 1)`). -/
theorem lemma_2 (θ ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (m : ℕ)
    (hm : ⌈Real.logb 2 (2 * Real.sqrt 2 / ε)⌉ ≤ (m : ℤ)) :
    ∃ n : Fin 4 → ℕ, ∑ j, n j = 2 ^ m ∧
      ‖(((n 0 : ℂ) - n 1) + Complex.I * ((n 2 : ℂ) - n 3)) / 2 ^ m
          - Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) / 2‖ ≤ ε := by sorry

end DepthOptQC.Synth
