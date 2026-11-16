-- Prove2me | Theorems.Thm_BordenaveCollins_exists_tail_le_of_rational_moments
-- name    : BordenaveCollins.exists_tail_le_of_rational_moments
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:08:54.725207+00:00
-- url     : https://prove2.me/theorems/745cad97-a9c1-4576-bea1-11f072d8363b
-- title:
--   The polynomial method — a tail bound of order 1/n² from rational moments with first-order support in [−ρ, ρ]
-- statement:
--   Let $K > 0$, let $c \ge 1$ be an integer, and for each $n$ let $E_n$ be a functional on real functions that is additive, homogeneous, monotone in the sense that $f \le g$ on $[-K, K]$ implies $E_n f \le E_n g$, and satisfies $E_n 1 \le 1$. Assume:
--
--   - **Rational moments.** There is a constant $C$ such that for every $q \ge 1$ there is a real polynomial $g_q$ of degree at most $Cq$ with $\tfrac12 \le g_q \le 1$ on $[0, 1/(Cq^2)]$, and for every real polynomial $h$ of degree at most $q$ a polynomial $f$ of degree at most $Cq$ with $E_n h = f\big(\tfrac{1}{cn}\big) / g_q\big(\tfrac{1}{cn}\big)$ for all $n \ge Cq$.
--   - **Zeroth and first order.** For every $p$, $E_n(x^p) \to a_p$ and $cn\,(E_n(x^p) - a_p) \to b_p$ as $n \to \infty$.
--   - **Growth.** There is $\rho \ge 0$ such that for every $\delta > 0$ there is a constant with $|a_p| \le \mathrm{const}\cdot(\rho + \delta)^p$ for all $p$, and likewise for $b_p$.
--
--   Then for every $\varepsilon > 0$ there is a constant $C'$ with
--   $$E_n\big(\mathbf 1_{\{|x| \ge \rho + \varepsilon\}}\big) \le \frac{C'}{n^2} \qquad\text{for all } n \ge 1.$$
--
--   This is the argument of Chen, Garza-Vargas, Tropp and van Handel, *A new approach to strong convergence* (the master inequalities of Theorems 6.1 and 7.1, and the proof of Theorem 3.9 on pp. 29–30), stated for an abstract sequence of positive functionals instead of the expected spectral distribution of a random matrix model. In an application $E_n f$ is the expected normalized trace of $f(X^N)$ for a self-adjoint random matrix $X^N$ of norm at most $K$ and size proportional to $N = cn$, and the conclusion bounds the expected proportion of eigenvalues outside $[-\rho - \varepsilon, \rho + \varepsilon]$.
--
--   **Formalization note.** The statement uses Mathlib only. The functionals are defined on all functions $\mathbb R \to \mathbb R$, and the hypotheses on $E_n$ are required for every $n \ge 0$. The constant $C$ of the first hypothesis is a natural number; for $C = 0$ the interval is read with Lean's convention $1/0 = 0$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 20-23, 29-30, Theorems 6.1 and 7.1 and the proof of Theorem 3.9, in an abstract form

import Mathlib

open Filter Topology Polynomial

namespace BordenaveCollins

theorem exists_tail_le_of_rational_moments (K : ℝ) (hK : 0 < K) (c : ℕ) (hc : 1 ≤ c)
    (E : ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ n f g, E n (f + g) = E n f + E n g)
    (hsmul : ∀ n (a : ℝ) f, E n (a • f) = a * E n f)
    (hmono : ∀ n f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E n f ≤ E n g)
    (hone : ∀ n, E n (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ n : ℕ, C * q ≤ n →
          E n (fun x => h.eval x) =
            f.eval (1 / ((c : ℝ) * n)) / gq.eval (1 / ((c : ℝ) * n)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a b : ℕ → ℝ)
    (ha : ∀ p : ℕ, Tendsto (fun n : ℕ => E n (fun x => x ^ p)) atTop (𝓝 (a p)))
    (hb : ∀ p : ℕ, Tendsto (fun n : ℕ => ((c : ℝ) * n) * (E n (fun x => x ^ p) - a p)) atTop
      (𝓝 (b p)))
    (hagrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |a p| ≤ C * (ρ + δ) ^ p)
    (hbgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |b p| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      E n (fun x => if ρ + ε ≤ |x| then 1 else 0) ≤ C / (n : ℝ) ^ 2 := by
  sorry

end BordenaveCollins
