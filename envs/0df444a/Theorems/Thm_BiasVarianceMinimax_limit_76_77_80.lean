-- Prove2me | Theorems.Thm_BiasVarianceMinimax_limit_76_77_80
-- name    : BiasVarianceMinimax.limit_76_77_80
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:12.454661+00:00
-- url     : https://prove2.me/theorems/73b2a354-bf88-4911-b0a8-fb75dcc1a102
-- title:
--   (77), (80) — the limit of problem (76)
-- statement:
--   The limit problem has the value
--
--   $$\min_{\tilde a:\ \frac{q_1}{q_1+q_2}\le K^{2(q_1+q_2)}\tilde a^2}|\tilde a|^{2q_2/(q_1+q_2)}\Big(\frac{q_1}{q_1+q_2}\Big)^{q_1/(q_1+q_2)}=\frac{q_1}{q_1+q_2}\,\frac1{K^{2q_2}}.$$
--
--   Moreover, let $a_n$ be an optimal solution of (24) for all large $n$, in any selection. Then
--
--   1. $|n^{q_1/(2(q_1+q_2))}a_n|\to\sqrt{q_1/(q_1+q_2)}\,(1/K^{q_1+q_2})$;
--   2. $n^{q_1/(q_1+q_2)}$ times the value of (24) tends to $\frac{q_1}{q_1+q_2}\frac1{K^{2q_2}}$;
--   3. $\eta^*\to K$.
--
--   The last item is why the calibration of Theorem 8 is $g(d)=Kd$.
--
--   Differences from the source:
--   - generalization: Appendix C assumes n₀ = 0 → the statement holds for every n₀ ∈ ℕ; reason: specializes to the page at n₀ = 0; Theorem 8 needs n₀
--   - encoding: ã∗ₙ an optimal solution of (76) → n^(q₁/(2(q₁+q₂))) aₙ with aₙ optimal for (24); reason: (76) is (24) after this rescaling of the variable, by p.55
--   - reading: "an optimal solution" at each n → every selection that is optimal for all large n; reason: (24) can be empty at finite n, and the page's argument applies to any selection
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, (77), p.55; (78)–(80), pp.55–56

import Mathlib
import Definitions.Def_BiasVarianceMinimax_IsOptimal
import Definitions.Def_BiasVarianceMinimax_weightStar

open Filter Topology

namespace BiasVarianceMinimax

/-- **The limit of (76).** Lam, Zhang & Zhang, arXiv:1902.04673v1, (77), p.55, and the argument to
(80), pp.55–56.

First clause: the limit problem (77) has value `(q₁/(q₁+q₂))(1/K^(2q₂))`. Second clause: for every
choice `a` of optimal solutions of (24) for large `n`, with `ãₙ = n^(q₁/(2(q₁+q₂))) aₙ`, one has
`|ãₙ| → √(q₁/(q₁+q₂)) (1/K^(q₁+q₂))`, the scaled value of (24) tends to the value of (77), and
`η∗ → K`.

**Formalization Note.** The second clause does not fix the sign of `aₙ` or a tie-breaking rule. The
scaled value of (24) at `aₙ` is the value of (76) at `ãₙ`. With the shift `n₀`. -/
theorem limit_76_77_80 (q₁ q₂ K : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hK : 0 < K) (n₀ : ℕ) :
    IsLeast {v : ℝ | ∃ b : ℝ, q₁ / (q₁ + q₂) ≤ K ^ (2 * (q₁ + q₂)) * b ^ 2 ∧
        v = |b| ^ (2 * q₂ / (q₁ + q₂)) * (q₁ / (q₁ + q₂)) ^ (q₁ / (q₁ + q₂))}
      (q₁ / (q₁ + q₂) * (1 / K ^ (2 * q₂))) ∧
    ∀ a : ℕ → ℝ, (∀ᶠ n in atTop, IsOptimal q₁ q₂ K n₀ n (a n)) →
      Tendsto (fun n : ℕ => |(n : ℝ) ^ (q₁ / (2 * (q₁ + q₂))) * a n|) atTop
        (𝓝 (Real.sqrt (q₁ / (q₁ + q₂)) * (1 / K ^ (q₁ + q₂)))) ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (q₁ / (q₁ + q₂)) * objective24 q₁ q₂ n₀ n (a n)) atTop
        (𝓝 (q₁ / (q₁ + q₂) * (1 / K ^ (2 * q₂)))) ∧
      Tendsto (fun n : ℕ => etaStar q₁ q₂ n₀ n (a n)) atTop (𝓝 K) := by sorry

end BiasVarianceMinimax
