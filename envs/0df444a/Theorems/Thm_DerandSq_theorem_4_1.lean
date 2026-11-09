-- Prove2me | Theorems.Thm_DerandSq_theorem_4_1
-- name    : DerandSq.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:15:55.095191+00:00
-- url     : https://prove2.me/theorems/06a05c24-fe2b-4c86-8a87-04a51ee6ace0
-- title:
--   Theorem 4.1 — for vertex-transitive $H$, $\mathbb P[\lambda(G^{\mathrm{rand}}(M^N)\circledS H) \geq \Lambda_H + \varepsilon] = o_N(1)$
-- statement:
--   Let $d \geq 3$ and $k \geq 1$, and let $H = ([d], E)$ be a $k$-regular vertex-transitive graph. For even $N$, let $M^N = (M^N_1, \dots, M^N_d)$ be a $d$-tuple of i.i.d. uniformly random $N \times N$ matching matrices and let $G^{\mathrm{rand}}(M^N)$ be the $d$-regular graph on $[N]$ with adjacency matrix $A^{\mathrm{rand}}(M^N) = \sum_{i=1}^d M^N_i$ and the canonical labelling $\mathrm{Out}_G(v, j) = M^N_j(v)$ of (4.1). Then for every $\varepsilon > 0$,
--   $$
--   \mathbb P_{M^N}\Bigl[\lambda\bigl(G^{\mathrm{rand}}(M^N) \circledS H\bigr) \geq \Lambda_H + \varepsilon\Bigr] = o_N(1)
--   $$
--   as $N \to \infty$ through even values, where $\lambda$ is the largest magnitude of a non-trivial eigenvalue of the adjacency matrix and $\Lambda_H$ is as in (4.3).
--
--   Together with the lower bound $\lambda(G \circledS H) \geq \Lambda_H - o(1)$ of Cohen, Cohen, Maor and Peled, this says that random graphs from the matching model are asymptotically optimal base graphs for derandomized squaring with every vertex-transitive auxiliary graph.
--
--   Differences from the source:
--   - reading: iid uniformly random matching matrices → uniform perfect matchings PM (fixed-point-free involutions) of Fin N, independent: uniform on Fin d → PM N; reason: Theorem 1.1 says "perfect matching matrices"; even N is only needed for perfect matchings
--   - reading: ε free in the display → every ε > 0; reason: as in (2.12) and (4.5)
--   - reading: o_N(1) for even N ∈ ℕ → limit along N = 2n, n → ∞, with d, H, ε fixed; reason: the probability is only defined for even N
--   - reading: G^rand(M^N) (labelling implicit) → the canonical labelling Out_G(v, j) = M_j(v) of (4.1); reason: §4 fixes this labelling throughout; Remark 4.4 uses π_j = M_j
--   - encoding: λ(·), the largest non-trivial eigenvalue magnitude → lam, the operator norm of (I − J)A(I − J); reason: A_S is symmetric with constant row sums dk, so the two agree (the paper's own A|_{⊥1}, p.12)
--   - encoding: x₀ the largest root of (4.4) → sSup of the real root set; reason: the set is finite and nonempty for d ≥ 3
--   - encoding: [d], the labels of H, the adjacency matrix of G Ⓢ H → Fin d (0-based); neighbour sets of H as Out_H; dsAdj with columns as tails; reason: relabellings that change no count; λ is invariant under transposition
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 4.1, p.19 (the conjecture [CCMP25, Conjecture 2.6], (4.5))

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_DerandSq_PM
import Definitions.Def_DerandSq_IsVertexTransitive
import Definitions.Def_DerandSq_dsAdj
import Definitions.Def_DerandSq_lam
import Definitions.Def_DerandSq_LambdaH

namespace DerandSq

/-- Theorem 4.1 of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.19 (the conjecture [CCMP25, Conjecture 2.6]). For every `k`-regular
vertex-transitive graph `H = ([d], E)` with `d ≥ 3`, `k ≥ 1`, and every `ε > 0`,
`P_{M^N}[ λ(G^rand(M^N) Ⓢ H) ≥ Λ_H + ε ] = o_N(1)` as `N → ∞` through even `N`, where
`M^N = (M_1^N, …, M_d^N)` is a `d`-tuple of i.i.d. uniformly random matching matrices,
`G^rand(M^N)` is the `d`-regular graph with adjacency matrix `∑_i M_i^N` and the canonical
labelling `Out_G(v, j) = M_j^N(v)` of (4.1), and `Λ_H` is as in (4.3).

**Formalization Note** Matching matrices are perfect matchings of `[N]` (`PM N`), sampled
uniformly and independently (uniform on `Fin d → PM N`); even `N` is `N = 2n`. `λ` is `lam`, the
norm of the adjacency matrix on `1^⊥`; the adjacency matrix of `G^rand(M^N) Ⓢ H` is
`dsAdj (fun j => M_j) H`. -/
theorem theorem_4_1 {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) (hvt : IsVertexTransitive H)
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => PunctSketch.coinProb (fun M : Fin d → PM (2 * n) =>
        LambdaH d H + ε ≤ lam (dsAdj (fun j => (M j).1) H)))
      Filter.atTop (nhds 0) := by sorry

end DerandSq
