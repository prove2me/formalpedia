-- Prove2me | Theorems.Thm_DerandSq_theorem_4_7
-- name    : DerandSq.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:11:00.573244+00:00
-- url     : https://prove2.me/theorems/4c51655f-0cb9-4324-ad03-65d12f631049
-- title:
--   Theorem 4.7 ([CCMP25], Corollary 5.7) — $\lim_p (c_{2p})^{1/2p} = \Lambda_H$ for the pruned graph $X$
-- statement:
--   Let $d \geq 3$ and let $H$ be a $k$-regular vertex-transitive graph on $[d]$ with $k \geq 1$. Let $X$ be the connected component of the root $e$ in $T_d \circledS H$ after removing one of the copies of $H$ adjacent to the root, and let $c_p$ be the number of closed walks of length $p$ originating at $e$ in $X$ (the coefficients of $C_H(z) = 1 + \sum_{p \geq 1} c_p z^p$, (4.11)). Then
--   $$
--   \lim_{p \to \infty} \bigl(c_{2p}\bigr)^{1/(2p)} = \Lambda_H ,
--   $$
--   with $\Lambda_H$ as in (4.3).
--
--   This is the analytic-combinatorics input of Cohen–Cohen–Maor–Peled; with Proposition 4.6 it gives the exact norm of $Q_H(u)$ (Corollary 4.8).
--
--   Differences from the source:
--   - reading: Let C(z) be as above (H, d, k from the surrounding text) → H k-regular and vertex-transitive on Fin d, d ≥ 3, k ≥ 1; reason: the hypotheses of §4 (vertex-transitive H, p.19) and the standing assumptions of §4.2 (p.21)
--   - reading: removing one of the copies adjacent to the root → for every i₀, the copy placed at the tree neighbour m_{i₀} of e is removed; reason: the paper picks an arbitrary copy; the statement holds for each choice
--   - encoding: X, the connected component of e → the whole graph after deleting the copy's edges (prunedX H i₀); reason: closed walks from e stay in the component of e, so c_p is unchanged
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 4.7, p.23 (X defined on p.22; hypotheses of §4, p.19, and §4.2, p.21)

import Mathlib
import Definitions.Def_DerandSq_IsVertexTransitive
import Definitions.Def_DerandSq_LambdaH
import Definitions.Def_DerandSq_prunedX
import Definitions.Def_DerandSq_closedWalks

namespace DerandSq

/-- Theorem 4.7 ([CCMP25], Corollary 5.7) of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.23. Let `H` be a `k`-regular
vertex-transitive graph on `[d]`, `d ≥ 3`, `k ≥ 1` (§4, p.19, and §4.2, p.21), and let `c_p` be
the number of length-`p` closed walks originating at the root `e` in the graph `X` obtained from
`T_d Ⓢ H` by removing one of the copies of `H` adjacent to the root (p.22). Then
`lim_{p → ∞} (c_{2p})^{1/(2p)} = Λ_H` with `Λ_H` as in (4.3).

**Formalization Note** The removed copy is the one placed at the tree neighbour `m_{i₀}` of the
root, for an arbitrary `i₀`; the statement is for every choice. -/
theorem theorem_4_7 {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) (hvt : IsVertexTransitive H) (i₀ : Fin d) :
    Filter.Tendsto
      (fun p : ℕ => (closedWalks (prunedX H i₀) 1 (2 * p) : ℝ) ^ ((1 : ℝ) / (2 * p)))
      Filter.atTop (nhds (LambdaH d H)) := by sorry

end DerandSq
