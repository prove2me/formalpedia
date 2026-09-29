-- Prove2me | Theorems.Thm_CandesTao_CompletionI_pair_counting
-- name    : CandesTao.CompletionI.pair_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:41:55.202987+00:00
-- url     : https://prove2.me/theorems/9c196ae7-1a3f-4636-aeea-9978a79a3502
-- title:
--   Lemma 5.2 — Pair counting: at most $O(j(k+1))^{2j(k+1)+q}$ strongly admissible pairs with $|Q'|=q$
-- statement:
--   There is an absolute constant $C > 0$ such that for all integers $j, k, q \ge 0$ the number $N(j,k,q)$ of strongly admissible pairs $(s,t)$ indexed by $[j]\times\{0,1\}\times\{0,\dots,k\}$ whose set $Q'$ of recycled non-rook moves has $|Q'| = q$ satisfies
--   $$N(j,k,q) \le \bigl(C\, j(k+1)\bigr)^{2j(k+1)+q}.$$
--
--   Combined with the exponent bound (Lemma 5.1), this bounds the sum over configurations in the expansion of $\mathbb E\operatorname{trace}(A^*A)^j$ by a geometric series in $q$, which converges once $n \ge c_0 j(k+1)$.
--
--   **Formalization Note** The paper writes the bound as $O(j(k+1))^{2j(k+1)+q}$ and defines $O(M)^M$ as $(CM)^M$ for an absolute constant $C$ (Section I-H); $C$ is therefore quantified before $j$, $k$ and $q$. At $j = 0$ the index set is empty, there is exactly one (empty) pair, and the bound reads $1 \le 0^0 = 1$.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2068, Lemma 5.2; O(M)^M convention p. 2059 (Section I-H)

import Definitions.Def_CandesTao_CompletionI_AdmissiblePair
import Mathlib.Data.Real.Basic

namespace CandesTao.CompletionI

/-- Candès–Tao, Lemma 5.2 (Pair Counting): there is an absolute constant `C > 0` such that
for all `j, k, q ≥ 0` the number of strongly admissible pairs `(s, t)` indexed by
`[j] × {0,1} × {0,…,k}` with `|Q'| = q` is at most `(C j (k+1))^(2j(k+1)+q)`
(the paper's `O(j(k+1))^{2j(k+1)+q}`, with `O(M)^M := (CM)^M`, Section I-H). -/
theorem pair_counting :
    ∃ C : ℝ, 0 < C ∧
      ∀ j k q : ℕ,
        (strongPairCount j k q : ℝ) ≤
          (C * ((j : ℝ) * ((k : ℝ) + 1))) ^ (2 * j * (k + 1) + q) := by sorry

end CandesTao.CompletionI
