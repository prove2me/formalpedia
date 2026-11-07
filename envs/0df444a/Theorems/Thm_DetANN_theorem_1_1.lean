-- Prove2me | Theorems.Thm_DetANN_theorem_1_1
-- name    : DetANN.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:37.300202+00:00
-- url     : https://prove2.me/theorems/03d722d5-d3da-4dd3-b9fd-0186945afa53
-- title:
--   Theorem 1.1 — deterministic $(1+\varepsilon)$-ANN with $n^{\mathrm{poly}(1/\varepsilon)}$ preprocessing and space and $O(d^2+d\,\mathrm{poly}(1/\varepsilon,\log n))$ query time
-- statement:
--   For every integer $d\ge1$, every $\varepsilon\in(0,1)$ and every set $P=\{P_0,\dots,P_{n-1}\}\subseteq\mathbb R^d$ of $n\ge d$ distinct points there is a fully deterministic data structure for $(1+\varepsilon)$-approximate nearest-neighbor search on $P$: every query $q\in\mathbb R^d$ is answered by a point $P_k$ with
--
--   $$\|q-P_k\|_2\le(1+\varepsilon)\min_{j}\|q-P_j\|_2 .$$
--
--   Its preprocessing time and space are $n^{\mathrm{poly}(\varepsilon^{-1})}$ and its query time is $O(d^2+d\,\mathrm{poly}(\varepsilon^{-1},\log n))$.
--
--   Precisely: there are deterministic real-RAM programs $\mathsf{Pre}$, $\mathsf{Qry}$ and constants $C,K\in\mathbb N$, fixed before the instance, such that for all $d,n,\varepsilon,P$ as above, preprocessing on input $(n,d,\varepsilon,P)$ halts within $C\,n^{K\varepsilon^{-K}}$ steps after storing to at most $C\,n^{K\varepsilon^{-K}}$ memory cells, and for every $q\in\mathbb R^d$ the query program halts within
--
--   $$C\big(d^2+d\,\varepsilon^{-K}(1+\log n)^K\big)$$
--
--   steps with such an index $k$.
--
--   This is the first deterministic data structure with polynomial space and $\mathrm{poly}(d,\log n)$ query time for $(1+\varepsilon)$-ANN in Euclidean space; before it, deterministic structures were known only for approximation $3+\varepsilon$.
--
--   **Formalization Note** The machine, the input and query layouts and the answer convention are those of `DetANN.IsDetANNStructure`.
--
--   Differences from the source:
--   - reading: a fully deterministic data structure (no machine named) → two programs of the published real RAM PNormReg.Machine without coin and rpow (rational literals, exact arithmetic and √, no floor), with the input/query layouts and answer convention of IsDetANNStructure; space = distinct cells stored to by preprocessing; reason: the paper counts arithmetic operations and names no machine; this is the standard deterministic real RAM, and a smaller instruction set makes the existence claim stronger
--   - reading: for each d, ε, P there is a data structure → one pair of programs and constants C, K for all instances, with ε an input; reason: the uniform reading is the stronger one and is how the paper's construction works (δ, τ, ℓ, L are computed from ε)
--   - reading: n^{poly(ε^{−1})} and O(d² + d poly(ε^{−1}, log n)) → C·n^{K·ε^{−K}} and C·(d² + d·ε^{−K}·(1 + log n)^K), natural log; reason: for ε < 1 every polynomial in ε^{−1} is at most K·ε^{−K} and every polynomial in (ε^{−1}, log n) at most C·ε^{−K}(1 + log n)^K; the factor C reads n^{poly} as O(n^{poly}), the only satisfiable reading at n = 1 where n^{poly} = 1
--   - encoding: a nonempty finite set P ⊆ ℝ^d of size n ≥ d; return a point of P → an injective list P : Fin n → ℝ^d with 1 ≤ d ≤ n; return an index k < n; reason: a finite set of size n is listed injectively; the index names the returned point
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Theorem 1.1, p.2 (PDF p.2)

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure

namespace DetANN

/-- **Theorem 1.1** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), p.2).
For every integer `d ≥ 1`, every `ε ∈ (0, 1)` and every set of `n ≥ d` points of `ℝ^d` there is a
fully deterministic data structure for `(1 + ε)`-approximate nearest-neighbor search, with
preprocessing time and space `n^{poly(1/ε)}` and query time `O(d² + d·poly(1/ε, log n))`.

**Formalization Note.** One pair of deterministic programs `Pre`, `Qry` and constants `C, K` serve
every instance: they are chosen before `d`, `n`, the points and `ε` (which is an input of
preprocessing). The point set is an injective list `P : Fin n → ℝ^d` and the answer is an index.
Preprocessing halts within `C·n^{K·ε^{−K}}` steps and stores to at most `C·n^{K·ε^{−K}}` cells; every
query `q ∈ ℝ^d` is answered within `C·(d² + d·ε^{−K}·(1 + log n)^K)` steps (`log` natural; `1 + log n`
avoids `log 1 = 0`). `poly(1/ε) ≤ K·ε^{−K}` and `poly(1/ε, log n) ≤ C·ε^{−K}(1 + log n)^K` for suitable
`C, K` when `ε < 1`, so these forms are equivalent to the printed ones. The machine and the
data-structure semantics are those of `DetANN.IsDetANNStructure`. -/
theorem theorem_1_1 :
    ∃ Pre Qry : PNormReg.Program, DetProgram Pre ∧ DetProgram Qry ∧
      ∃ C K : ℕ, ∀ d n : ℕ, 1 ≤ d → d ≤ n →
        ∀ P : Fin n → EuclideanSpace ℝ (Fin d), Function.Injective P →
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            IsDetANNStructure Pre Qry P ε (1 + ε)
              ((C : ℝ) * (n : ℝ) ^ ((K : ℝ) * ε⁻¹ ^ K))
              ((C : ℝ) * (n : ℝ) ^ ((K : ℝ) * ε⁻¹ ^ K))
              ((C : ℝ) * ((d : ℝ) ^ 2 + d * ε⁻¹ ^ K * (1 + Real.log n) ^ K)) := by sorry

end DetANN
