-- Prove2me | Theorems.Thm_DerandSq_Supplement_theorem_3_4
-- name    : DerandSq.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:07:26.159208+00:00
-- url     : https://prove2.me/theorems/91b2b5c6-ed7a-4144-8011-0fcb46c2f5e7
-- title:
--   Theorem 3.4 — $\mathbb P[\lambda(A^{\mathrm{rand}}_{\mathrm{rot}}) \ge \|a\| + \varepsilon] \lesssim \frac1N (d^{2k}4k\log(r+k)/\varepsilon)^8 \log(ed^{2k}/\varepsilon)$
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $r \ge 1$, $k \ge 1$, $N \in \mathbb N$, $d = 2r$, and let $U^N = (U_1, \dots, U_r)$ and $V^N = (V_1, \dots, V_{k-1})$ be independent tuples of i.i.d. uniformly random $N \times N$ permutation matrices. Let $A^{\mathrm{rand}} = \sum_{j} (U_j + U_j^*)$ be the random $d$-regular graph of the permutation model and $A^{\mathrm{rand}}_{\mathrm{rot}}(U^N, V^N)$ its rotating walk (3.1) with rotations $V^N$. For every $\varepsilon$ with
--
--   $$
--   0 < \varepsilon < d^{2k} - \frac{(k+1)^{k+1}}{k^k}(d-1)d^{k-1},
--   $$
--
--   we have
--
--   $$
--   \mathbb P_{U^N, V^N}\Bigl[\lambda\bigl(A^{\mathrm{rand}}_{\mathrm{rot}}(U^N, V^N)\bigr) \ge \frac{(k+1)^{k+1}}{k^k}(d-1)d^{k-1} + \varepsilon\Bigr] \le \frac{C}{N}\Bigl(\frac{d^{2k}\cdot 4k \cdot \log(r+k)}{\varepsilon}\Bigr)^{8}\log\frac{e\,d^{2k}}{\varepsilon}.
--   $$
--
--   Here $\lambda$ is the largest magnitude of a non-trivial eigenvalue. Since $C$ does not depend on $r$, $k$ or $\varepsilon$, the bound remains meaningful when $k$ and $d$ grow with $N$: the rotating walk on a random graph with random rotations almost meets the lower bound of Cohen–Cohen–Maor–Peled with high probability.
--
--   **Formalization Note** The paper's $\lesssim$ is read as $\le C \cdot (\dots)$ with one absolute constant. $\lambda(X)$ is the operator norm of $(I - J)X(I - J)$, $J = \mathbf 1\mathbf 1^{\top}/N$.
--
--   Differences from the source:
--   - reading: ≲ (no constant is given; the text before the theorem lets k and d grow with N) → ∃ C > 0 quantified before r, k, N and ε; reason: every dependence on r, k, d, N and ε is printed, so the implicit constant is absolute; a constant depending on the parameters would be weaker
--   - encoding: U^N, V^N independent tuples of i.i.d. uniform permutation matrices → uniform probability (PunctSketch.coinProb) on (Fin r → Perm (Fin N)) × (Fin (k − 1) → Perm (Fin N)); reason: the product of uniform laws is the uniform law on the product; same probabilities
--   - encoding: d = 2r, r ≥ 1, k ≥ 1 (standing assumptions of §3) → d written 2 * r, hypotheses 1 ≤ r and 1 ≤ k; reason: same instances; for r = k = 1 the range of ε is empty in both
--   - encoding: λ(A_rot), the largest non-trivial eigenvalue magnitude → DerandSq.lam (rotWalk (permModelAdj U) V) = ‖(I − J) A_rot (I − J)‖; reason: A_rot is symmetric with constant row sums d^{2k}, so both are the same number
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 3.4, p.17

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_DerandSq_lam
import Definitions.Def_DerandSq_Supplement_permModelAdj
import Definitions.Def_DerandSq_Supplement_rotWalk

namespace DerandSq.Supplement

/-- Theorem 3.4 of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.17. There is an absolute constant `C > 0` such that for all
`r ≥ 1`, `k ≥ 1`, `N`, with `d = 2r` and `c_{r,k} = (k+1)^{k+1}/k^k · (d − 1) d^{k−1}`, and every
`ε` with `0 < ε < d^{2k} − c_{r,k}`,
`P_{U^N, V^N}[ λ(A^rand_rot(U^N, V^N)) ≥ c_{r,k} + ε ]
  ≤ C · (1/N) · (d^{2k} · 4k · log(r + k) / ε)^8 · log(e d^{2k} / ε)`,
where `A^rand = A^rand(U^N) = ∑_j (U_j + U_j^*)` is the random `d`-regular graph of the
permutation model and `A^rand_rot` its rotating walk (3.1) with rotations `V^N`.

**Formalization Note** The paper's `≲` is read as `≤ C · (…)` with one absolute constant `C`,
quantified before `r`, `k`, `N` and `ε` (the text before the theorem: "we can let `k` and
`d` grow with the number of vertices `N`"). `U^N = (U_1, …, U_r)` and `V^N = (V_1, …, V_{k−1})`
are independent tuples of i.i.d. uniform permutations of `[N]`: a uniform element of the
product type, probability `PunctSketch.coinProb`. `λ` is `DerandSq.lam`. At `N = 0` the
right side is `0` (Lean's `1/0 = 0`) and so is the left side (`λ` of the empty matrix is
`0`). For `r = k = 1` the range of `ε` is empty. -/
theorem theorem_3_4 : ∃ C : ℝ, 0 < C ∧ ∀ (r k N : ℕ), 1 ≤ r → 1 ≤ k → ∀ ε : ℝ, 0 < ε →
    ε < (2 * (r : ℝ)) ^ (2 * k) -
      ((k : ℝ) + 1) ^ (k + 1) / (k : ℝ) ^ k * (2 * (r : ℝ) - 1) * (2 * (r : ℝ)) ^ (k - 1) →
    PunctSketch.coinProb
        (fun UV : (Fin r → Equiv.Perm (Fin N)) × (Fin (k - 1) → Equiv.Perm (Fin N)) =>
          ((k : ℝ) + 1) ^ (k + 1) / (k : ℝ) ^ k * (2 * (r : ℝ) - 1) * (2 * (r : ℝ)) ^ (k - 1) + ε ≤
            DerandSq.lam (rotWalk (permModelAdj UV.1) UV.2)) ≤
      C * (1 / (N : ℝ)) *
        ((2 * (r : ℝ)) ^ (2 * k) * (4 * (k : ℝ)) * Real.log ((r : ℝ) + k) / ε) ^ 8 *
        Real.log (Real.exp 1 * (2 * (r : ℝ)) ^ (2 * k) / ε) := by sorry

end DerandSq.Supplement
