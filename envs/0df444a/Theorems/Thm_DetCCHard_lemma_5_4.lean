-- Prove2me | Theorems.Thm_DetCCHard_lemma_5_4
-- name    : DetCCHard.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:55.682168+00:00
-- url     : https://prove2.me/theorems/a2fde9e9-cb12-48ff-9156-acc53d48a8fc
-- title:
--   Lemma 5.4 — the initial matrix: $D(R_0) = d_0$, $\mathrm{rank}(R_0) = p_0 = 2^{d_0-1}$, $\mathcal P(R_0; 2^{-L}, d_0)$, polynomial size
-- statement:
--   For $L \ge 1$ let $p_0 = \mathrm{pow2}(64(L+1))$ and $R_0(z, j) = z_j$ on $\{0,1\}^{p_0} \times [p_0]$, with uniform input weights. Then, with $d_0 := \log p_0 + 1$,
--   $$
--   D(R_0) = d_0, \qquad \operatorname{rank}(R_0) = p_0 = 2^{d_0 - 1}, \qquad \mathcal P(R_0; 2^{-L}, d_0).
--   $$
--   For $L = \lceil \log n \rceil$ and $n \ge 4$, the initial matrix has polynomial size in $n$ and can be printed in polynomial time.
--
--   The initial matrix starts the iteration of Proposition 5.5.
--
--   **Formalization Note** Rank is over $\mathbb R$. Size is the number of entries $2^{p_0} p_0$. Printing is a polynomial-time string function from $n$ in unary to the explicit $2^{p_0} \times p_0$ table $(r, j) \mapsto$ bit $j$ of $r$, which is $R_0$ with row $z$ relabelled by the number $\sum_j z_j 2^j$ (a bijection; verification file).
--
--   Differences from the source:
--   - encoding: the initial matrix printed → the explicit table (r, j) ↦ bit j of r on [2^{p₀}] × [p₀]; reason: a bijective relabelling of the rows of R₀
--   - encoding: polynomial in n → n given in unary; size as 2^{p₀}p₀ ≤ n^c; reason: same meaning
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 5.4, p.17 (proof in §A.4, p.55)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_realRank
import Definitions.Def_DetCCHard_pow2
import Definitions.Def_DetCCHard_CodeSym
import Definitions.Def_DetCCHard_WMat

namespace DetCCHard

/-- **Lemma 5.4 (Initial matrix)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256
ad552d13…a4a03, Lemma 5.4, p.17). For `L ≥ 1`, let `p₀ = pow2(64(L + 1))` and `R₀(z, j) = z_j` on
`{0, 1}^{p₀} × [p₀]`, with uniform input weights. Then `d₀ := log p₀ + 1`, `D(R₀) = d₀`,
`rank(R₀) = p₀ = 2^{d₀ − 1}`, and `P(R₀; 2^{-L}, d₀)`. For `L = ⌈log n⌉` and `n ≥ 4`, the initial
matrix has polynomial size in `n` and can be printed in polynomial time.

**Formalization Note** `log p₀ = Nat.log 2 p₀` (`p₀` is a power of two); rank is over `ℝ`. Size is
the number of entries `2^{p₀} p₀`. "Printed in polynomial time" is a string function,
polynomial-time in the sense of the published `CookPvsNP.PolyTimeComputable`, from `n` in unary
to the explicit encoding of the `2^{p₀} × p₀` table `(r, j) ↦ bit j of r`, which is `R₀` with row
`z` relabelled by the number `r = ∑_j z_j 2^j` (a bijection). `n` is read in unary, so
"polynomial in `n`" is polynomial in the input length. -/
theorem lemma_5_4 :
    (∀ L : ℕ, 1 ≤ L →
      let p₀ := pow2 (64 * (L + 1))
      let d₀ := Nat.log 2 p₀ + 1
      Dcost (initialMatrix L).entry = d₀ ∧ realRank (initialMatrix L).entry = p₀ ∧
        p₀ = 2 ^ (d₀ - 1) ∧
        DeletionBounds (initialMatrix L).entry (initialMatrix L).μX (initialMatrix L).μY
          (1 / 2 ^ L) d₀) ∧
    (∃ c : ℕ, ∀ n : ℕ, 4 ≤ n →
      2 ^ pow2 (64 * (Nat.clog 2 n + 1)) * pow2 (64 * (Nat.clog 2 n + 1)) ≤ n ^ c) ∧
    ∃ f : List Unit → List CodeSym, CookPvsNP.PolyTimeComputable f ∧
      ∀ n : ℕ, 4 ≤ n →
        f (List.replicate n ()) =
          encodeTable (fun (r : Fin (2 ^ pow2 (64 * (Nat.clog 2 n + 1))))
            (j : Fin (pow2 (64 * (Nat.clog 2 n + 1)))) => (r : ℕ).testBit j) := by sorry

end DetCCHard
