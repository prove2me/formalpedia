-- Prove2me | Theorems.Thm_AMPUniversality_Universal_eq_4_15
-- name    : AMPUniversality.Universal.eq_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:41.646888+00:00
-- url     : https://prove2.me/theorems/35963df6-612e-4b51-b8ed-dad3dbe29c03
-- title:
--   (4.15), p. 20 — a sub-Gaussian variable with scale factor C/N has E|X|ˢ ≤ 2C^{s/2}(s/e)^{s/2}N^{−s/2}
-- statement:
--   Let $C > 0$, let $N \ge 1$ be an integer, and let $X$ be a real random variable that is sub-Gaussian with scale factor $C/N$:
--
--   $$
--   \mathbb E\, e^{\lambda X} \;\le\; e^{C\lambda^2/(2N)} \qquad\text{for all } \lambda\in\mathbb R .
--   $$
--
--   Then for every real $s > 0$ the absolute moment $\mathbb E|X|^s$ is finite and
--
--   $$
--   \mathbb E|X|^s \;\le\; 2\, C^{s/2} \Big(\frac{s}{e}\Big)^{s/2} N^{-s/2}.
--   $$
--
--   In the paper this is applied to every entry $A_{ij}$, $i < j$, of the random matrix of a $(C,d)$-regular sequence (Definition 4); it provides the $N^{-\mu/2}$ decay (4.17) of the expected products of matrix entries along trees in the proof of Proposition 1.
--
--   **Formalization Note** The statement is posed for a single random variable on a probability space; the paper's $A_{ij}$ is the instance $X = A_{ij}(N)$. The hypothesis $N \ge 1$ is implicit on the page (entries $A_{ij}$ with $i < j \in [N]$ exist only for $N \ge 2$). The first, $\lambda$-dependent, bound of the display is the proof and is not stated. Integrability of $|X|^s$ is stated as a conclusion so that the inequality cannot hold through the junk value $0$ of a non-integrable Bochner integral.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 20, (4.15)

import Mathlib

namespace AMPUniversality.Universal

open MeasureTheory ProbabilityTheory

/-- (4.15), p. 20: a real random variable `X` that is sub-Gaussian with scale factor `C/N`
(`E e^{λX} ≤ e^{Cλ²/(2N)}` for all real `λ`) has, for every real `s > 0`, an integrable
`|X|^s` with `E|X|^s ≤ 2 C^{s/2} (s/e)^{s/2} N^{-s/2}`. -/
theorem eq_4_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (C : ℝ) (hC : 0 < C) (N : ℕ) (hN : 0 < N)
    (hX : HasSubgaussianMGF X (Real.toNNReal (C / N)) P) (s : ℝ) (hs : 0 < s) :
    Integrable (fun ω => |X ω| ^ s) P ∧
      ∫ ω, |X ω| ^ s ∂P ≤
        2 * C ^ (s / 2) * (s / Real.exp 1) ^ (s / 2) * (N : ℝ) ^ (-(s / 2)) := by sorry

end AMPUniversality.Universal
