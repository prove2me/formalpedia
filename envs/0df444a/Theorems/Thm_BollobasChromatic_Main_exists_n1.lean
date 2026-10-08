-- Prove2me | Theorems.Thm_BollobasChromatic_Main_exists_n1
-- name    : BollobasChromatic.Main.exists_n1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:08:16.849878+00:00
-- url     : https://prove2.me/theorems/7cac8e46-b229-4b75-a853-346e02a7bce9
-- title:
--   Proof of Theorem 4, p. 53 — n₁ with 2n₁^{5/3} ≤ E_q(n₁,s₁) ≤ 3n₁^{5/3} and n/(log n)³ ≤ n₁ = O(n/(log n)²)
-- statement:
--   Let $0<p<1$ be fixed, $q=1-p$, $d=1/q$, $s_0=[2\log_d n-\log_d\log_d n+2\log_d(e/2)+1]$ and $s_1=s_0-\lfloor 5\log_d\log n\rfloor$. There is a constant $C>0$ (depending on $p$) such that for all large $n$ there is a natural number $n_1$ with
--   $$
--   2n_1^{5/3}\le E_q(n_1,s_1)=\binom{n_1}{s_1}q^{\binom{s_1}2}\le 3n_1^{5/3}
--   \qquad\text{and}\qquad
--   \frac{n}{(\log n)^3}\le n_1\le C\,\frac{n}{(\log n)^2}.
--   $$
--
--   These $n_1$ and $s_1$ are the parameters $n'$ and $r'$ to which Corollary 3 is applied, for $G_q$, in the proof of Theorem 4.
--
--   **Formalization Note** The page defines $n_1$ as the "maximal" natural number with $E_q(n_1,s_1)\ge 2n_1^{5/3}$; the set of such numbers is upward closed, so "minimal" is meant, and only the existence of an $n_1$ with the listed properties is used. The page asserts $n_1\le n/(\log n)^2$; with the constant $1$ this is false for every fixed $p$ (Stirling's formula gives $n_1\sim K n/(\log n)^2$ with $K>1$; an exact computation for $p\in\{0.05,\dots,0.99\}$ and $n$ up to $10^{10000}$ gives ratios between $1.6$ and $98$). The statement therefore has an unspecified constant $C$, which is all the proof of Theorem 4 needs. $s_1$ is converted to $\mathbb N$ by truncation at $0$; $s_1>0$ for all large $n$.
-- source:
--   Bollobás, The chromatic number of random graphs, Combinatorica 8 (1988), p. 53, proof of Theorem 4 (definition of s_1 and n_1)

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

namespace BollobasChromatic.Main

open Filter Topology Asymptotics

theorem exists_n1 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∃ n1 : ℕ,
      2 * (n1 : ℝ) ^ ((5 : ℝ) / 3) ≤ expCliques n1 (1 - p) (s1 p n).toNat ∧
      expCliques n1 (1 - p) (s1 p n).toNat ≤ 3 * (n1 : ℝ) ^ ((5 : ℝ) / 3) ∧
      (n : ℝ) / Real.log (n : ℝ) ^ 3 ≤ n1 ∧
      (n1 : ℝ) ≤ C * n / Real.log (n : ℝ) ^ 2 := by sorry

end BollobasChromatic.Main
