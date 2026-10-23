-- Prove2me | Theorems.Thm_CorrClusterExp_IBR_proposition_3_1
-- name    : CorrClusterExp.IBR.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:01.753115+00:00
-- url     : https://prove2.me/theorems/6752fd2f-c37a-4234-befd-a59e199fcb72
-- title:
--   Proposition 3.1, p. 13 — optimal experiments with equal-sized clusters: σ, worst cases, V^OPT = n²/(4(n−1)), (n+1)/4, h* + h*(h*−1)σ, and 4V^OPT/n → 1
-- statement:
--   Let $0<q\le\tfrac12$ and consider $n\ge 2$ clusters of equal size $w_i=1$. Let $P$ be the experiment that, with probability $p=\lceil qn\rceil-qn$, treats a uniformly random set of $\lfloor qn\rfloor$ clusters and, with probability $1-p$, a uniformly random set of $\lceil qn\rceil$ clusters. Then $P$ is an experiment with marginals $q$ that solves (1), i.e. its worst-case variance equals $V^{\mathrm{OPT}}$, and:
--
--   1. **When $qn\in\mathbb N$** ($p=0$: a uniformly random set of $qn$ clusters is treated). The correlation of any two distinct assignments is $\sigma=-\frac{1}{n-1}$. If $n$ is even, every $y$ with $n/2$ coordinates equal to $1$ and the rest $0$ is a worst case and
--   $$V^{\mathrm{OPT}}=\frac14\,\frac{n^2}{n-1};$$
--   if $n$ is odd, every $y$ with $(n+1)/2$ or $(n-1)/2$ coordinates equal to $1$ and the rest $0$ is a worst case and $V^{\mathrm{OPT}}=\frac{n+1}{4}$.
--   2. **When $qn\notin\mathbb N$.** The correlation of any two distinct assignments is
--   $$
--   \sigma=-\frac{nq(1-q)-p(1-p)}{n(n-1)q(1-q)}\in\Big(-\frac1{n-1},0\Big).
--   $$
--   If $h^*\in\mathbb N$ is an integer closest to $\min\{-\frac{1}{2\sigma}+\frac12,\ n\}$, then every $y$ with $h^*$ coordinates equal to $1$ and the rest $0$ is a worst case and $V^{\mathrm{OPT}}=h^*+h^*(h^*-1)\sigma$.
--
--   Moreover, $\lim_{n\to\infty}4V^{\mathrm{OPT}}/n=1$.
--
--   The proposition shows that for equal sizes the best experiment treats all clusters symmetrically, and that its worst-case variance is about $n/4$, a factor $4$ below the independent assignment.
--
--   **Formalization Note** "$h$ clusters take $y_i=1$ in the worst case" is stated as: the indicator of every $h$-element set of clusters maximizes $y^\top\Sigma(P)y$ over the box $[0,1]^n$ (`IsMaxOn`); the experiment is exchangeable, so all such indicators have the same value, and other maximizers are not excluded. $p$ and $\sigma$ are given as variables equal to their defining expressions.
--
--   Differences from the source:
--   - encoding: $n$ clusters → $n\ge 2$; reason: $\sigma$ has $n-1$ in a denominator and for $n=1$ the statement is undefined (no pair of clusters).
--   - reading: "in the worst case, $h$ clusters take $y_i=1$ and the rest $y_i=0$" → the indicator of every $h$-subset is a maximizer on the box; reason: the experiment is exchangeable, so the page names no particular subset; uniqueness is not claimed.
--   - reading: "the integer closest to $x$" → any natural $h^*$ with $|h^*-x|\le|h-x|$ for all integers $h$; reason: at a tie two integers are closest and both give the same value.
--   - encoding: the two experiments of cases 1 and 2 → one law `fracLaw q n`; reason: for $qn\in\mathbb N$, $p=0$ and it is the uniform $qn$-subset of case 1.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 13, Proposition 3.1

import Mathlib
import Definitions.Def_CorrClusterExp_IBR_Setting

namespace CorrClusterExp.IBR

open Matrix Finset

theorem proposition_3_1 (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1 / 2) :
    (∀ n : ℕ, 2 ≤ n →
      IsExperiment q (fracLaw q n) ∧
      worstCase (corr q (fracLaw q n)) (fun _ : Fin n => (1 : ℝ)) =
        VOPT q (fun _ : Fin n => (1 : ℝ)) ∧
      ((∃ m : ℕ, q * n = m) →
        (∀ i k : Fin n, i ≠ k → corr q (fracLaw q n) i k = -1 / ((n : ℝ) - 1)) ∧
        (Even n →
          (∀ s : Finset (Fin n), 2 * s.card = n →
            IsMaxOn (fun y => y ⬝ᵥ (corr q (fracLaw q n) *ᵥ y)) (box fun _ : Fin n => (1 : ℝ))
              (fun i => if i ∈ s then (1 : ℝ) else 0)) ∧
          VOPT q (fun _ : Fin n => (1 : ℝ)) = 1 / 4 * ((n : ℝ) ^ 2 / ((n : ℝ) - 1))) ∧
        (Odd n →
          (∀ s : Finset (Fin n), (2 * s.card = n + 1 ∨ 2 * s.card + 1 = n) →
            IsMaxOn (fun y => y ⬝ᵥ (corr q (fracLaw q n) *ᵥ y)) (box fun _ : Fin n => (1 : ℝ))
              (fun i => if i ∈ s then (1 : ℝ) else 0)) ∧
          VOPT q (fun _ : Fin n => (1 : ℝ)) = ((n : ℝ) + 1) / 4)) ∧
      ((¬ ∃ m : ℕ, q * n = m) →
        ∀ p σ : ℝ, p = (⌈q * n⌉₊ : ℝ) - q * n →
          σ = -((n * q * (1 - q) - p * (1 - p)) / (n * (n - 1) * q * (1 - q))) →
          (∀ i k : Fin n, i ≠ k → corr q (fracLaw q n) i k = σ) ∧
          -1 / ((n : ℝ) - 1) < σ ∧ σ < 0 ∧
          ∀ hstar : ℕ,
            (∀ h : ℤ, |(hstar : ℝ) - min (-1 / (2 * σ) + 1 / 2) (n : ℝ)| ≤
              |(h : ℝ) - min (-1 / (2 * σ) + 1 / 2) (n : ℝ)|) →
            (∀ s : Finset (Fin n), s.card = hstar →
              IsMaxOn (fun y => y ⬝ᵥ (corr q (fracLaw q n) *ᵥ y)) (box fun _ : Fin n => (1 : ℝ))
                (fun i => if i ∈ s then (1 : ℝ) else 0)) ∧
            VOPT q (fun _ : Fin n => (1 : ℝ)) = hstar + hstar * ((hstar : ℝ) - 1) * σ)) ∧
    Filter.Tendsto (fun n : ℕ => 4 * VOPT q (fun _ : Fin n => (1 : ℝ)) / n)
      Filter.atTop (nhds 1) := by sorry

end CorrClusterExp.IBR
