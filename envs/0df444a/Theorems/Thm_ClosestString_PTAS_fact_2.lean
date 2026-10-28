-- Prove2me | Theorems.Thm_ClosestString_PTAS_fact_2
-- name    : ClosestString.PTAS.fact_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T16:19:05.290283+00:00
-- url     : https://prove2.me/theorems/8a100217-08d6-4a6a-a659-9e1c80d11f1b
-- title:
--   Fact 2 with (13)–(14) — with probability ≥ 1 − 2(nm)^{−1/3}, d(s∗, t′_i) ≤ d(s∗, t_i) + 2ε|P| for all i
-- statement:
--   Fix strings $s_1,\dots,s_n$ ($n\ge1$) of length $m$, $1\le L\le m$, an admissible tuple $t_{i_1},\dots,t_{i_r}$ of length-$L$ substrings (Figure 3, step 1) with agreement set $Q$ and $P=\{1,\dots,L\}\setminus Q$, a string $s$ of length $L$, length-$L$ substrings $t_i$ of $s_i$, and $\varepsilon>0$. Let $s^*$ be the string with $s^*|_P=s|_P$ and $s^*|_Q=t_{i_1}|_Q$. Let $R$ be the multiset of $\lceil(4/\varepsilon^2)\ln(nm)\rceil$ independent uniform positions of $P$ (step 1(b)), and for each $i$ let $t'_i$ be any length-$L$ substring of $s_i$ that minimizes the objective of step 1(c)(i) for $y=s|_R$,
--   $$d(y,t'|_R)\cdot\frac{|P|}{|R|}+d(t_{i_1}|_Q,t'|_Q).$$
--   Then, with probability at least $1-2(nm)^{-1/3}$ over $R$,
--
--   $$d(s^*,t'_i)\ \le\ d(s^*,t_i)+2\varepsilon|P|\qquad\text{for all }1\le i\le n.$$
--
--   In the proof of Theorem 9, $s$ is an optimal center, $t_i$ the substrings closest to it and the tuple the one of Fact 1; then the substrings $t'_i$ found from the sample are almost as close to $s^*$ as the optimal ones. The probability bound is the last sentence of the proof (p. 11), obtained from (13)–(14).
--
--   Differences from the source:
--
--   - generalization: s an optimal center, t_i the substrings closest to s, t_{i1},…,t_{ir} satisfying Fact 1 → any string s, any substrings t_i of s_i, any admissible tuple; reason: the proof of Fact 2 uses none of these properties; the paper's choice is a special case
--   - generalization: t′_i "defined as in step 1(c)(i)" → t′_i = sel R i for any selection sel that minimizes the step-1(c)(i) objective for every R and i; reason: covers every tie-breaking rule, in particular the smallest-start rule of the algorithm's definition
--   - reading: "With high probability" → probability at least 1 − 2(nm)^{−1/3}; reason: the value the proof derives (p. 11)
--   - reading: log(nm) → Real.log, the natural logarithm; reason: (11) needs exp(−ε²|R|/2) ≤ (nm)^{−2}, i.e. |R| ≥ (4/ε²) ln(nm), which is exactly the printed computation with ln
--   - encoding: R a multiset of uniformly random positions from P → sampleLaw P k: product of k uniform laws on P; the Dirac mass at the constant multiset 0 when P = ∅; reason: when P = ∅ the sample is never read (weight |P|/|R| = 0) and the event holds surely; same instances
--   - encoding: positions 1..L, s_1..s_n, substrings → 0-based Fin L, Fin n; substrings by start position p with p + L ≤ m; real-valued objective; reason: relabelling; changes no instance
-- source:
--   Li, Ma & Wang, On the Closest String and Substring Problems, arXiv:cs/0002012v1, p. 10, Fact 2 (proof pp. 10–11; probability 1 − 2(nm)^(−1/3) in the last sentence of the proof, p. 11)

import Mathlib
import Definitions.Def_ClosestString_PTAS_Algorithm

namespace ClosestString.PTAS

/-- **Fact 2** with (13)–(14) (Li, Ma & Wang, arXiv:cs/0002012v1, statement p. 10, probability in the
last sentence of its proof, p. 11), for any center `s` of length `L`, any substrings `t_i` of the
`s_i` (start positions `t i`), any admissible tuple `τ` and any `ε > 0`: let `P = P_τ`,
`s∗ = s` on `P` and `t_{i1}` on `Q_τ`, and let `t′_i = sel R i` be any substring that step 1(c)(i)
of Figure 3 may choose for `y = s|R` (any minimizer of the step-1(c)(i) objective). Over the random multiset `R` of `⌈(4/ε²) ln(nm)⌉` independent
uniform positions of `P`, with probability at least `1 − 2(nm)^{−1/3}`,
`d(s∗, t′_i) ≤ d(s∗, t_i) + 2ε|P|` for all `i`. -/
theorem fact_2 {A : Type*} [Fintype A] [DecidableEq A] {n m L r : ℕ} [NeZero n] [NeZero L]
    [NeZero r] (S : Fin n → Fin m → A) (hL : L ≤ m) (τ : AdmTuple n m L r) (s : Fin L → A)
    (t : Fin n → Start m L) (ε : ℝ) (hε : 0 < ε)
    (sel : (Fin (sampleSize n m ε) → Fin L) → Fin n → Start m L)
    (hsel : ∀ R i p, score S τ (fun a => s (R a)) R i (sel R i) ≤ score S τ (fun a => s (R a)) R i p) :
    ENNReal.ofReal (1 - 2 * ((n : ℝ) * m) ^ (-(1 / 3 : ℝ))) ≤
      sampleLaw (diffP S τ) (sampleSize n m ε)
        {R | ∀ i : Fin n,
          (hammingDist (splice (diffP S τ) s (firstStr S τ))
              (substr (S i) (sel R i)) : ℝ)
            ≤ hammingDist (splice (diffP S τ) s (firstStr S τ)) (substr (S i) (t i))
              + 2 * ε * (diffP S τ).card} := by sorry

end ClosestString.PTAS
