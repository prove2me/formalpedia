-- Prove2me | Theorems.Thm_BipColorHard_lemma_10
-- name    : BipColorHard.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:40.282747+00:00
-- url     : https://prove2.me/theorems/39f08c12-8dab-4309-8ab5-2d063b81eb5b
-- title:
--   Lemma 10 — the connector's positive correlation
-- statement:
--   Let $q=2k+1\ge3$ and let $A_0,B_0\in\Omega$ be disjoint. For every sufficiently large $s$, depending only on $q$, the connector $K$ satisfies $K(B,A)>0$ for all $B\in X$ and $A\in Y$, and, for $(B,A)\in X\times Y$ chosen with probability proportional to $K(B,A)$,
--   $$\Pr[B=B_0]=\Pr[A=A_0]\quad\text{and}\quad\Pr[B=B_0,A=A_0]>\Pr[B=B_0]\Pr[A=A_0].$$
--   Moreover, for every $u\in(0,1/k)$ there is $L_0$ such that the same holds with $K_L(B,A)$ in place of $K(B,A)$, for every integer $L\ge L_0$.
--
--   The positive correlation is what produces the antiferromagnetic interaction between blocks in Lemma 11.
--
--   Differences from the source:
--   - encoding: fixed disjoint $A_0,B_0$ → every disjoint pair, with $s_0$ and $L_0$ uniform over the pairs; reason: the manuscript's pair is arbitrary, and there are finitely many pairs
--   - encoding: probabilities → ratios of sums of the weights; reason: the distribution is defined by proportionality
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 10, pp.10–11 (PDF pp.12–13)

import Definitions.Def_BipColorHard_Connector

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 10**, pp.10–11 (PDF pp.12–13), manuscript sha256 78a66d1f…, for `q = 2k + 1 ≥ 3` and disjoint `A₀, B₀ ∈ Ω`. For every sufficiently
large `s`, depending only on `q`, the connector `K` satisfies `K(B, A) > 0` for all `B ∈ X` and `A ∈ Y`, and, for `(B, A) ∈ X × Y` chosen with
probability proportional to `K(B, A)`, `Pr[B = B₀] = Pr[A = A₀]` and `Pr[B = B₀, A = A₀] > Pr[B = B₀] Pr[A = A₀]`. Moreover, for every
`u ∈ (0, 1/k)` there is `L₀` such that the same holds with `K_L(B, A)` in place of `K(B, A)`, for every integer `L ≥ L₀`.

**Formalization Note.** `A₀, B₀` are fixed but arbitrary in the manuscript; `s₀` and `L₀` are stated uniformly over the finitely many
pairs, which is what "depending only on `q`" means. -/
theorem lemma_10 (k : ℕ) (hk : 1 ≤ k) :
    ∃ s₀ : ℕ, ∀ s, s₀ ≤ s →
      (∀ A0 B0 : Omega k, Disjoint A0.1 B0.1 → ConnCorr (connK k s A0 B0) A0 B0) ∧
      ∀ u : ℝ, 0 < u → u < 1 / (k : ℝ) → ∃ L₀ : ℕ, ∀ L, L₀ ≤ L →
        ∀ A0 B0 : Omega k, Disjoint A0.1 B0.1 → ConnCorr (connKL k s u L A0 B0) A0 B0 := by sorry

end BipColorHard
