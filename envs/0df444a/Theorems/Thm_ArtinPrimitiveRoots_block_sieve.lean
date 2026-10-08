-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_block_sieve
-- name    : ArtinPrimitiveRoots.block_sieve
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T09:27:02.248453+00:00
-- url     : https://prove2.me/theorems/e42a907a-affa-4c4c-8f75-b9a6f22edee2
-- title:
--   Lemma 11.1 (OpenAI) — block sieve
-- statement:
--   Fix $\eta_0 > 0$ and a real $C_0$. Consider the following data: a finite set $\mathcal A$ with weights $\omega(a) \ge 0$; a real $z \ge 2$ and a finite set $\mathcal P$ of primes $p \le z$; a bad condition `bad p a` for each prime $p$ and $a \in \mathcal A$; a real $X' \ge 0$; and values $g(p)$ with $0 \le g(p) \le 1 - \eta_0$ for $p \in \mathcal P$ and $\sum_{p \in \mathcal P,\ v < p \le v^2} g(p) \le C_0$ for every real $v > 1$. For $d \ge 1$ let $A(d)$ be the total weight of the $a \in \mathcal A$ that satisfy the bad condition at every prime $p \mid d$, put $g(d) = \prod_{p \mid d} g(p)$ and $E(d) = A(d) - X'g(d)$, and let $S$ be the total weight of the $a \in \mathcal A$ satisfying no bad condition at any $p \in \mathcal P$.
--
--   1. There are $H_0$ and $B$ such that for every even integer $H \ge H_0$ and all such data,
--   $$\Bigl|S - X'\prod_{p \in \mathcal P}(1 - g(p))\Bigr| \le B\,X'\prod_{p \in \mathcal P}(1 - g(p))\,e^{-H} + B\sum_{d \mid \prod_{p \in \mathcal P} p,\ d \le z^{4H+2}} |E(d)|.$$
--   2. There is $B$ such that for all such data,
--   $$S \le B\Bigl(X'\prod_{p \in \mathcal P}(1 - g(p)) + \sum_{d \mid \prod_{p \in \mathcal P} p,\ d \le z^{10}} |E(d)|\Bigr).$$
--
--   $H_0$ and the constants $B$ depend only on $\eta_0$ and $C_0$.
--
--   **Formalization note.** On the squarefree products $d$ of primes of $\mathcal P$ (the divisors of $\prod_{p \in \mathcal P} p$), “$g(1) = 1$ and $g$ multiplicative” is encoded by $g(d) = \prod_{p \mid d} g(p)$, and $E(d)$ is defined as $A(d) - X'g(d)$, so the decomposition $A(d) = X'g(d) + E(d)$ is a definition rather than a hypothesis. The two $O$-terms of (11.2) share one constant $B$. A set of primes at most $z$ is finite, so $\mathcal P$ is a `Finset`.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 70: “Lemma 11.1 (Block sieve). Let $\mathcal A$ be a finite set with nonnegative weights, and let $\mathcal P$ be a set of primes at most $z$, where $z \ge 2$. For each $p \in \mathcal P$, specify a bad condition on $\mathcal A$. Suppose that, for every squarefree product $d$ of primes in $\mathcal P$, the weight of the objects satisfying all conditions at $p \mid d$ is $A(d) = X'g(d) + E(d)$, including $d = 1$, where $X' \ge 0$, $g(1) = 1$, and $g$ is multiplicative. Assume that, for fixed constants $\eta_0 > 0$ and $C_0 < \infty$, $0 \le g(p) \le 1 - \eta_0$, $\sum_{v<p\le v^2,\ p \in \mathcal P} g(p) \le C_0$ $(v > 1)$. (11.1) For every sufficiently large even integer $H$, the weight $S$ of objects avoiding all the bad conditions satisfies $S = X'\prod_{p \in \mathcal P}(1 - g(p))\bigl(1 + O(\exp(-H))\bigr) + O\Bigl(\sum_{d \le z^{4H+2},\ d \mid \prod_{p \in \mathcal P} p} |E(d)|\Bigr)$. (11.2) The constants and the lower bound on $H$ depend only on $\eta_0, C_0$. In particular, the estimate is uniform when $H$ grows. For $H = 2$ there is the upper bound $S \ll_{\eta_0, C_0} X'\prod_{p \in \mathcal P}(1 - g(p)) + \sum_{d \le z^{10},\ d \mid \prod_{p \in \mathcal P} p} |E(d)|$. (11.3)”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 70, Lemma 11.1

import Mathlib

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem block_sieve (η₀ C₀ : ℝ) (hη₀ : 0 < η₀) :
    (∃ H₀ : ℕ, ∃ B : ℝ, ∀ H : ℕ, H₀ ≤ H → Even H →
      ∀ {α : Type*} (Aset : Finset α) (ω : α → ℝ), (∀ a ∈ Aset, 0 ≤ ω a) →
      ∀ (z : ℝ), 2 ≤ z → ∀ Pset : Finset ℕ, (∀ p ∈ Pset, p.Prime ∧ (p : ℝ) ≤ z) →
      ∀ bad : ℕ → α → Prop, ∀ X' : ℝ, 0 ≤ X' → ∀ g : ℕ → ℝ,
        (∀ p ∈ Pset, 0 ≤ g p ∧ g p ≤ 1 - η₀) →
        (∀ v : ℝ, 1 < v → ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀) →
      let A : ℕ → ℝ := fun d => ∑ a ∈ Aset.filter (fun a => ∀ p ∈ d.primeFactors, bad p a), ω a
      let E : ℕ → ℝ := fun d => A d - X' * ∏ p ∈ d.primeFactors, g p
      let S : ℝ := ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a
      |S - X' * ∏ p ∈ Pset, (1 - g p)| ≤
        B * (X' * ∏ p ∈ Pset, (1 - g p)) * exp (-(H : ℝ)) +
          B * ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (4 * H + 2)), |E d|) ∧
    (∃ B : ℝ, ∀ {α : Type*} (Aset : Finset α) (ω : α → ℝ), (∀ a ∈ Aset, 0 ≤ ω a) →
      ∀ (z : ℝ), 2 ≤ z → ∀ Pset : Finset ℕ, (∀ p ∈ Pset, p.Prime ∧ (p : ℝ) ≤ z) →
      ∀ bad : ℕ → α → Prop, ∀ X' : ℝ, 0 ≤ X' → ∀ g : ℕ → ℝ,
        (∀ p ∈ Pset, 0 ≤ g p ∧ g p ≤ 1 - η₀) →
        (∀ v : ℝ, 1 < v → ∑ p ∈ Pset.filter (fun p : ℕ => v < p ∧ (p : ℝ) ≤ v ^ 2), g p ≤ C₀) →
      let A : ℕ → ℝ := fun d => ∑ a ∈ Aset.filter (fun a => ∀ p ∈ d.primeFactors, bad p a), ω a
      let E : ℕ → ℝ := fun d => A d - X' * ∏ p ∈ d.primeFactors, g p
      let S : ℝ := ∑ a ∈ Aset.filter (fun a => ∀ p ∈ Pset, ¬ bad p a), ω a
      S ≤ B * (X' * ∏ p ∈ Pset, (1 - g p) +
          ∑ d ∈ (∏ p ∈ Pset, p).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ (10 : ℕ)), |E d|)) := by
  sorry

end ArtinPrimitiveRoots
