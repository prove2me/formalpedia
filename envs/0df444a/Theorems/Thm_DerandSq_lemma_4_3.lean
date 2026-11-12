-- Prove2me | Theorems.Thm_DerandSq_lemma_4_3
-- name    : DerandSq.lemma_4_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T06:00:48.8402+00:00
-- url     : https://prove2.me/theorems/a181ad72-acda-4d5f-b81a-62312f00bb04
-- title:
--   Lemma 4.3 — $M_S = \frac{1}{dk}\sum_{\{i,j\}\in E(H)}(\lambda(\pi_i)\lambda(\pi_j)+\lambda(\pi_j)\lambda(\pi_i))$ and $A_S = Q_H(\Pi^N)$
-- statement:
--   Let $\pi_1, \dots, \pi_d$ be permutations of $[N]$, let $G$ be the $d$-regular graph with $A_G = \sum_j \lambda(\pi_j)$ and the labelling $\mathrm{Out}_G(v, j) = \pi_j(v)$ of (4.1), let $H$ be a $k$-regular graph on $[d]$, and let $S = G \circledS H$. Then
--   $$
--   M_S = \frac{1}{dk} \sum_{\{i,j\} \in E(H)} \bigl(\lambda(\pi_i)\lambda(\pi_j) + \lambda(\pi_j)\lambda(\pi_i)\bigr), \tag{4.8}
--   $$
--   and, writing $\Pi^N_i = \lambda(\pi_i)$,
--   $$
--   A_S = Q_H(\Pi^N) = \sum_{\{i,j\} \in E(H)} \bigl(\Pi^N_i \Pi^N_j + \Pi^N_j \Pi^N_i\bigr). \tag{4.9}
--   $$
--   So the adjacency matrix of the derandomized square is a quadratic polynomial in the permutation matrices of $G$, which is what allows strong convergence to be applied to it.
--
--   Differences from the source:
--   - generalization: π₁, …, π_d occurring in the decomposition (4.1) of a d-regular graph G → any d-tuple of permutations of Fin N; reason: every decomposition (4.1) is such a tuple, so the statement specializes to the source's
--   - reading: Π^N = (λ(π1),...,λ(πn)) → (λ(π_1), …, λ(π_d)); reason: the index n is a typo for d; the tuple has one entry per label
--   - encoding: sum over unordered edges {i, j} ∈ E(H) → sum over ordered pairs i < j with H.Adj i j; reason: each unordered edge is counted once either way
--   - encoding: λ(π) and the adjacency matrix A_S → permMat π with entry (w, v) = [π v = w]; dsAdj with columns as tails; reason: the paper's orientation λ(π)δ_v = δ_{πv}; labels are Fin d
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Lemma 4.3, p.21, displays (4.8) and (4.9)

import Mathlib
import Definitions.Def_DerandSq_permMat
import Definitions.Def_DerandSq_dsAdj
import Definitions.Def_DerandSq_dsWalk

namespace DerandSq

/-- Lemma 4.3 of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.21. Let `S = G Ⓢ H` be the derandomized square of the graph `G`
labelled by permutations `π_1, …, π_d` of `[N]` (`Out_G(v, j) = π_j(v)`, (4.1)) via a `k`-regular
graph `H` on `[d]`. Then (4.8) `M_S = (1/dk) ∑_{{i,j} ∈ E(H)} (λ(π_i)λ(π_j) + λ(π_j)λ(π_i))` and
(4.9) `A_S = Q_H(Π^N) = ∑_{{i,j} ∈ E(H)} (Π_i Π_j + Π_j Π_i)` with `Π_i = λ(π_i)`.

**Formalization Note** `λ(π)` is `permMat π` (`λ(π) δ_v = δ_{π v}`); each unordered edge is
summed once as the pair `i < j`. The paper takes `π` from a decomposition (4.1) of a `d`-regular
graph; the statement is for every `d`-tuple of permutations. -/
theorem lemma_4_3 {N d k : ℕ} (H : SimpleGraph (Fin d)) [DecidableRel H.Adj]
    (hH : H.IsRegularOfDegree k) (π : Fin d → Equiv.Perm (Fin N)) :
    dsWalk π H k = ((d : ℝ) * k)⁻¹ • ∑ i : Fin d, ∑ j : Fin d,
        (if i < j ∧ H.Adj i j then
          permMat (π i) * permMat (π j) + permMat (π j) * permMat (π i) else 0) ∧
      dsAdj π H = ∑ i : Fin d, ∑ j : Fin d,
        (if i < j ∧ H.Adj i j then
          permMat (π i) * permMat (π j) + permMat (π j) * permMat (π i) else 0) := by sorry

end DerandSq
