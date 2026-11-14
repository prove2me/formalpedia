-- Prove2me | Theorems.Thm_DetANN_walk_family_uniform
-- name    : DetANN.walk_family_uniform
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:26:32.281387+00:00
-- url     : https://prove2.me/theorems/89529fb0-2957-4ac3-b9fa-46e5b51a0339
-- title:
--   §7.2, p.17 — in the walk family every block occurs $\Delta^\ell$ times and $\mathbb P[V=v\mid I=i]=(W^\ell)_{iv}$
-- statement:
--   Let $G$ be an undirected $\Delta$-regular multigraph on $[d]$ ($\Delta\ge1$) with normalized adjacency matrix $W$, and let $\ell\ge0$. For each start vertex $v$ list the endpoints of all $\Delta^\ell$ walks of length $\ell$ from $v$. Then
--
--   1. every vertex $i$ is the endpoint of exactly $t=\Delta^\ell$ of the pairs (start vertex, walk), so a uniform occurrence $I$ of a uniform tuple $S_V$ is uniform on $[d]$;
--   2. for all $i,v$,
--   $$\mathbb P[V=v\mid I=i]=\frac{\#\{\text{walks from }v\text{ ending at }i\}}{\Delta^\ell}=(W^\ell)_{iv}.$$
--
--   This is what makes the walk family a valid tuple family for the §5 estimates and what feeds the spectral bound into Lemma 7.2.
--
--   Differences from the source:
--   - generalization: the graph of Lemma 7.1 and a positive integer ℓ → any undirected Δ-regular multigraph on [d] with Δ ≥ 1, and any ℓ ≥ 0; reason: the graph of Lemma 7.1 is such a graph; ℓ ≥ 1 is a special case
--   - encoding: the conditional probability P[V = v | I = i] → #{walks from v ending at i}/Δ^ℓ, using clause 1 for the number Δ^ℓ of pairs with I = i; reason: this is the conditional probability under the uniform choice
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §7.2, p.17 (PDF p.17)

import Mathlib
import Definitions.Def_DetANN_Multigraph
import Definitions.Def_DetANN_TupleFamily

namespace DetANN

/-- **The walk family** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §7.2, p.17).
For an undirected `Δ`-regular multigraph on `[d]` with normalized adjacency matrix `W` and any `ℓ`:
every vertex `i` is the endpoint of exactly `t = Δ^ℓ` of the pairs (start `v`, length-`ℓ` walk `w`), so
`I` is uniform on `[d]`; and `P[V = v | I = i] = #{w : walk w from v ends at i}/Δ^ℓ = (W^ℓ)_{iv}`.

**Formalization Note.** `Δ ≥ 1` is assumed (the paper: `Δ ≥ 2`). Walks are words
`Fin ℓ → Fin Δ` and `walkEnd nbr ℓ v w` is the endpoint. `W^ℓ` is the matrix power. -/
theorem walk_family_uniform {d Δ : ℕ} (nbr : Fin d → Fin Δ → Fin d) (hΔ : 1 ≤ Δ)
    (hund : IsUndirected nbr) (ℓ : ℕ) :
    (∀ i : Fin d, blockCount (walkEnd nbr ℓ) i = Δ ^ ℓ) ∧
      ∀ i v : Fin d,
        ((Finset.univ.filter fun w : Fin ℓ → Fin Δ => walkEnd nbr ℓ v w = i).card : ℝ) /
            (Δ : ℝ) ^ ℓ = (adjMatrix nbr ^ ℓ) i v := by sorry

end DetANN
