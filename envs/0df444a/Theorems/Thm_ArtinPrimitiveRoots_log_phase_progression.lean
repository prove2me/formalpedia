-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_log_phase_progression
-- name    : ArtinPrimitiveRoots.log_phase_progression
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T12:51:29.741101+00:00
-- url     : https://prove2.me/theorems/2e10c576-dda8-4f0e-a482-cf7bbef75ba2
-- title:
--   Lemma 3.3 of OpenAI's Prime Predecessors paper — a logarithmic phase on progressions, Σ_{n∈I, n≡a (q)} n^{iv} ≪ (N′/q) exp(−L/T^{C₃})
-- statement:
--   There are constants $C_3 > 0$ and $K$ such that the following holds for every $C > 0$, with $L = \log x$ and $T = \log L$. There is $x_0$ such that for every $x \ge x_0$, every real $N'$ with $\exp(L/T^2) \le N' \le 2x^5$, every integer $q$ with $1 \le q \le L^C$, every real $v$ with $\exp(L/(2T^2)) \le |v| \le 4x^3$, every residue $a$ modulo $q$, and every interval $J \subseteq [N', 2N']$,
--
--   $$\Bigl|\sum_{\substack{n \in J\\ n \equiv a \ (\mathrm{mod}\ q)}} n^{iv}\Bigr| \le K\,\frac{N'}{q}\,\exp\bigl(-L/T^{C_3}\bigr),$$
--
--   the sum running over positive integers. $C_3$ and $K$ are absolute; $x_0$ depends on $C$.
--
--   This is a result of OpenAI's companion paper, taken here as an input. That paper proves it by Vinogradov's mean value method (§3, pp. 7–8). The primitive-roots paper uses it for the second range of (10.19) in the proof of Proposition 10.3 (p. 69). The same estimate, with the same ranges, is Lemma 2.4 of OpenAI's *The Poisson–Dirichlet law for prime predecessors*.
--
--   **Formalization note.** The paper says only that $C_3$ is absolute; its $\ll$ carries no subscript, so the implicit constant $K$ is also taken absolute, chosen before $C$. A residue $a$ modulo $q$ is a natural number $a$, with $n \equiv a \pmod q$ (`Nat.ModEq`); every class has such a representative. "An interval $I \subset [N', 2N']$" is any order-connected set $J \subseteq [N', 2N']$, and "$q \le L^C$" is read as $1 \le q \le L^C$.
--
--   OpenAI, *Prime Predecessors with an Even Number of Prime Factors* (2026), p. 7: “Lemma 3.3 (A logarithmic phase on progressions). Fix $C > 0$. There is an absolute constant $C_3 > 0$ such that, for sufficiently large $x$ in terms of $C$, the following holds uniformly: $\exp(L/T^2) \le N' \le 2x^5$, $q \le L^C$, $\exp(L/(2T^2)) \le |v| \le 4x^3$. For every residue $a \pmod q$ and every interval $I \subset [N', 2N']$, $\Bigl|\sum_{n \in I,\ n \equiv a\ (\mathrm{mod}\ q)} n^{iv}\Bigr| \ll \frac{N'}{q}\exp(-L/T^{C_3})$. (3.7)” Section 3 sets $L = \log x$ and $T = \log L$ (p. 4).
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 69: “The second range uses the logarithmic-phase estimate of [22, Lemma 3.3], valid for arbitrary residue classes and subintervals.”
-- source:
--   OpenAI, Prime Predecessors with an Even Number of Prime Factors, OpenAI Math Release preprint, September 17, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/paper.pdf (Apache-2.0), p. 7, Lemma 3.3 (a logarithmic phase on progressions), as used for (10.19) of the primitive-roots paper (p. 69)

import Mathlib

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem log_phase_progression :
    ∃ C₃ K : ℝ, 0 < C₃ ∧ ∀ C : ℝ, 0 < C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ N : ℝ, exp (log x / log (log x) ^ 2) ≤ N → N ≤ 2 * x ^ 5 →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ log x ^ C →
      ∀ v : ℝ, exp (log x / (2 * log (log x) ^ 2)) ≤ |v| → |v| ≤ 4 * x ^ 3 →
      ∀ a : ℕ, ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc N (2 * N) →
        ‖∑ n ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD q]),
            (if (n : ℝ) ∈ J then (n : ℂ) ^ (Complex.I * v) else 0)‖ ≤
          K * (N / q) * exp (-(log x / log (log x) ^ C₃)) := by
  sorry

end ArtinPrimitiveRoots
