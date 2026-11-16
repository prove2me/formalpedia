-- Prove2me | Theorems.Thm_DerandSq_Supplement_theorem_3_3
-- name    : DerandSq.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:06:52.034181+00:00
-- url     : https://prove2.me/theorems/1dea804c-04f8-4916-a779-d6eab7ae9644
-- title:
--   Theorem 3.3 (Norm of the Infinite Rotating Tree) — $\|a\| = \frac{(k+1)^{k+1}}{k^k}(d-1)d^{k-1}$, $d = 2r$
-- statement:
--   Let $r \ge 1$ and $k \ge 1$, put $d = 2r$, and let $a$ be the infinite rotating tree (3.4) in the reduced C*-algebra of the free group $F_{r+k-1}$:
--
--   $$
--   a = t v_1 t v_2 t \cdots v_{k-1} t^2 v_{k-1}^* \cdots v_2^* t v_1^* t, \qquad t = \sum_{j=1}^r (u_j + u_j^*),
--   $$
--
--   with $u_j, v_i$ the left-regular images of the free generators. Then
--
--   $$
--   \|a\|_{C^*_{\mathrm{red}}(F_{k+r-1})} = \frac{(k+1)^{k+1}}{k^k}\,(d-1)\,d^{k-1}.
--   $$
--
--   For $k = 1$ this is $\|t\|^2 = 4(d-1)$ (Kesten). In general the value is the limit of the spectral expansion of the rotating walk on random $d$-regular graphs, and it matches, up to $o_N(1)$, the lower bound of Cohen–Cohen–Maor–Peled for every choice of rotations.
--
--   **Formalization Note** The reduced norm is the operator norm on $\ell^2(F_{r+k-1})$, with $F_{r+k-1}$ = `FreeGroup (Fin r ⊕ Fin (k-1))`.
--
--   Differences from the source:
--   - reading: d = 2r with T_d the infinite d-regular tree (r not bounded explicitly) → hypothesis 1 ≤ r; reason: §3 builds t from r free generators as the adjacency operator of the infinite tree T_d; for r = 0 the operator is 0 while the formula is nonzero at k = 1
--   - encoding: k ≥ 1 with rotations h_1, …, h_{k−1} → hypothesis 1 ≤ k, rotations indexed by Fin (k − 1); reason: standing assumption of §3; excludes only the undefined k = 0
--   - encoding: ‖a‖ in C*_red(F_{k+r−1}) → operator norm of rotTree r (k − 1) on ℓ²(FreeGroup (Fin r ⊕ Fin (k − 1))); reason: the reduced C*-norm is the operator norm on ℓ²; same value
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 3.3, p.16

import Mathlib
import Definitions.Def_DerandSq_Supplement_rotTree

namespace DerandSq.Supplement

/-- Theorem 3.3 (Norm of the Infinite Rotating Tree) of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.16. Let `r ≥ 1`, `k ≥ 1`,
`d = 2r`, and let `a` be the infinite rotating tree (3.4) in `F_{r+k−1}`. Then
`‖a‖_{C*_red(F_{k+r−1})} = (k+1)^{k+1}/k^k · (d − 1) d^{k−1}`.

**Formalization Note** `a` is `rotTree r (k - 1)`; the reduced C*-norm is the operator norm on
`ℓ²(F_{r+k−1})` (`C*_red` is the norm closure of the span of `λ(F_{r+k−1})` inside the bounded
operators). `d = 2r` is written `2 * r`. `r ≥ 1` because `T_d` with `d = 2r` is the infinite
`d`-regular tree (for `r = 0` the operator is `0` and the formula is not). -/
theorem theorem_3_3 (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ‖rotTree r (k - 1)‖ =
      ((k : ℝ) + 1) ^ (k + 1) / (k : ℝ) ^ k * (2 * (r : ℝ) - 1) * (2 * (r : ℝ)) ^ (k - 1) := by sorry

end DerandSq.Supplement
