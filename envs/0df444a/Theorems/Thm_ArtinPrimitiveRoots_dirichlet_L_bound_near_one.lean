-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_dirichlet_L_bound_near_one
-- name    : ArtinPrimitiveRoots.dirichlet_L_bound_near_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T15:46:18.867131+00:00
-- url     : https://prove2.me/theorems/a8cdaf72-fd11-4626-a4ba-0c21a47c75f8
-- title:
--   Lemma 3.4 of OpenAI's Prime Predecessors paper — near Re s = 1 and up to height 3x³, |L(s, χ)| ≤ exp(K (log log x)²) for characters of modulus at most (log x)^C
-- statement:
--   Fix $C > 0$ and write $L = \log x$, $T = \log L$. There are $K$ and $x_0$ such that for every $x \ge x_0$, every integer $q$ with $1 \le q \le L^C$, every Dirichlet character $\chi$ modulo $q$, and all reals $\sigma, v$ with $|\sigma - 1| \le 10T^4/L$ and $1/2 \le |v| \le 3x^3$,
--
--   $$|L(\sigma + iv, \chi)| \le \exp(KT^2),$$
--
--   where $L(s, \chi)$ is Mathlib's analytically continued Dirichlet $L$-function (`DirichletCharacter.LFunction`).
--
--   A step toward `long_prime_polynomial` (Lemma 3.1 of the same paper). The paper proves it from the logarithmic-phase estimate `log_phase_progression` (Lemma 3.3).
--
--   **Formalization note.** The paper's "$\log|D(\sigma + iv, \chi)| \ll_C T^2$" is used only as an upper bound (in Jensen's formula), and is stated here as $|D| \le \exp(KT^2)$. The modulus condition $q \ge 1$ is written `[NeZero q]`.
--
--   OpenAI, *Prime Predecessors with an Even Number of Prime Factors* (2026), p. 8: “Lemma 3.4 (A bound near the line Re s = 1). Fix $C > 0$ and put $r_* = T^4/L$. Uniformly for $q \le L^C$, $\log|D(\sigma + iv, \chi)| \ll_C T^2$ $\bigl(|\sigma - 1| \le 10r_*,\ \tfrac12 \le |v| \le 3x^3\bigr)$. (3.14)”
-- source:
--   OpenAI, Prime Predecessors with an Even Number of Prime Factors, OpenAI Math Release preprint, September 17, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf (Apache-2.0), p. 8, Lemma 3.4 (a bound near the line Re s = 1), (3.14)

import Mathlib

namespace ArtinPrimitiveRoots

open Real

theorem dirichlet_L_bound_near_one (C : ℝ) (hC : 0 < C) :
    ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ log x ^ C →
      ∀ χ : DirichletCharacter ℂ q, ∀ σ v : ℝ,
        |σ - 1| ≤ 10 * (log (log x) ^ 4 / log x) → 1 / 2 ≤ |v| → |v| ≤ 3 * x ^ 3 →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ≤
          exp (K * log (log x) ^ 2) := by
  sorry

end ArtinPrimitiveRoots
