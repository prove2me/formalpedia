-- Prove2me | Theorems.Thm_FasterSFM_lemma_4
-- name    : FasterSFM.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:41.891188+00:00
-- url     : https://prove2.me/theorems/7faf5ca0-740c-433f-9dab-052ddbe7c028
-- title:
--   Lemma 4 — historical cuts remain valid after parameter updates and contractions
-- statement:
--   Let $h:2^U\to\mathbb R$ be submodular. Let $\tilde D$ be the quotient DAG at the time a vector was stored and $D_i$ the current one: every current block is a union of old blocks (the merge map $\mu$), and every $D_i$-closed set pulls back to a $\tilde D$-closed set with the same lift. Let $\tilde t\le t_i$ be the stored and the current sliding parameters, with $h(\emptyset),h(U)\ge h(\emptyset)+1-\tilde t$.
--
--   Let $\tilde a$ be the greedy vector of $H_{\tilde t}$ on $\tilde D$ for an ordering of the old blocks, mapped to $D_i$ by summing over merged blocks. Then:
--
--   1. for every proper nonempty $D_i$-closed set $X$,
--   $$\tilde a(X)\ \le\ H_{t_i}(X)-(t_i-\tilde t);$$
--   2. if $\tilde a=0$, then $H_{t_i}\ge0$ on all $D_i$-closed sets, and, when the invariant (1) holds at $t_i$ and $h(\emptyset),h(U)\ge h(\emptyset)+1-t_i$, the witness value $h(\emptyset)+1-t_i$ is the minimum of $h$;
--   3. for an old arc $u\to v$, the graph vector $e_u-e_v$ mapped to $D_i$ satisfies $\tilde g_{uv}(X)\le0$ for every $D_i$-closed set $X$.
--
--   The lemma lets the cutting-plane method keep every earlier cut after the sliding parameter grows and after strongly connected components are contracted.
--
--   Differences from the source:
--   - generalization: the quotient DAGs at two times, arcs only added → any two block structures D₀, D with a merge map μ (D.blk = μ ∘ D₀.blk) such that every D-closed set pulls back to a D₀-closed set; reason: this is what "arcs are only added" gives in the proof; the quotient DAGs are an instance (reading R8)
--   - generalization: the greedy vector of the oracle's ordering (decreasing weight, ties descendant-first) → the greedy vector of any ordering σ of the old blocks; reason: the proof uses only that a greedy vector lies in B(H_t̃)
--   - reading: the algorithm's context (h(∅), h(U) ≥ m at time t̃; the parameter only increases) → hypotheses EndpointsAbove h t̃ and t̃ ≤ t_i; reason: reading R7: the algorithm's facts made explicit
--   - reading: "the algorithm can terminate since a minimum has been found" → under invariant (1) at t_i and EndpointsAbove h t_i, h(∅) + 1 − t_i ≤ h(Y) for every Y; reason: reading R7: the witness attains m, so this is "a minimum has been found"
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 4, p.12

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_FasterSFM_BlockDAG

namespace FasterSFM

open Classical

/-- **Lemma 4** (Historical cuts remain valid), p.12.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 4, p.12.

"Let ã be a stored greedy vector constructed by a prior oracle call, mapped to the vertices of the
current DAG by summing the values on the vertices that were merged during contractions. Let t̃ be ã's
timestamp. For every proper nonempty D_i-closed set X, we have ã(X) ≤ H_{t_i}(X) − (t_i − t̃).
If ã = 0 then H_{t_i} is non-negative on all D_i-closed sets and the algorithm can terminate since a
minimum has been found. For a stored graph vector g̃_uv mapped to the current DAG by summing the
values on the vertices that were merged during contractions, we have g̃_uv(X) ≤ 0 for every D_i-closed
set X."

The old DAG `D₀` (blocks `Fin N₀`) and the current DAG `D` (blocks `Fin N`) partition the same ground
set `Fin n`; `μ` sends each old block to the current block containing it, and every `D`-closed set
pulls back to a `D₀`-closed set (arcs are only added over time). The stored greedy vector is the greedy
vector `g(π(j)) = H_{t̃}(P_j) − H_{t̃}(P_{j−1})` of the old `H_{t̃}` for an ordering with position map `σ`
(`SchrijverSFM.Alg.greedy`), and the stored graph vector is `e_u − e_v` for an old arc `u → v`.

**Formalization Note.**
* Reading R8: the quotient DAGs are any block structures related by such a merge map `μ`; the
  ordering of the greedy vector is any ordering (the paper's is by decreasing weight with ties broken
  descendant-first; the proof uses only membership in the base polytope).
* Reading R7: `EndpointsAbove h t̃` (the witness value at time `t̃` is at most `h(∅)` and `h(U)`,
  which makes `H_{t̃}` submodular) and `t̃ ≤ t_i` (the parameter only increases) are the algorithm's
  facts, stated as hypotheses.
* "The algorithm can terminate since a minimum has been found" is stated as: if moreover the invariant
  (1) holds at `t_i` (every `Y ⊆ U` with `h_s(Y) ≤ 0` for some `s ≥ t_i` is the lift of a closed set)
  and `EndpointsAbove h t_i`, then the witness value `m = h(∅) + 1 − t_i` is the minimum of `h`. -/
theorem lemma_4 {n N₀ N : ℕ} (h : Finset (Fin n) → ℝ) (hsub : NonmonotoneSubmod.Shared.Submodular h)
    (D₀ : BlockDAG n N₀) (D : BlockDAG n N) (μ : Fin N₀ → Fin N)
    (hμ : ∀ u, D.blk u = μ (D₀.blk u))
    (hpull : ∀ X, D.Closed X → D₀.Closed (Finset.univ.filter fun C => μ C ∈ X))
    (t₀ ti : ℝ) (hend₀ : EndpointsAbove h t₀) (hti : t₀ ≤ ti) (σ : Equiv.Perm (Fin N₀)) :
    (∀ X : Finset (Fin N), D.Closed X → X.Nonempty → X ≠ Finset.univ →
      setSum (pushVec μ (SchrijverSFM.Alg.greedy (D₀.Hs h t₀) σ)) X ≤ D.Hs h ti X - (ti - t₀)) ∧
    (pushVec μ (SchrijverSFM.Alg.greedy (D₀.Hs h t₀) σ) = 0 →
      (∀ X : Finset (Fin N), D.Closed X → 0 ≤ D.Hs h ti X) ∧
      (EndpointsAbove h ti →
        (∀ s : ℝ, ti ≤ s → ∀ Y : Finset (Fin n), h Y - h ∅ - 1 + s ≤ 0 →
          ∃ X, D.Closed X ∧ Y = D.lift X) →
        ∀ Y : Finset (Fin n), h ∅ + 1 - ti ≤ h Y)) ∧
    (∀ u v : Fin N₀, D₀.arc u v → ∀ X : Finset (Fin N), D.Closed X →
      setSum (pushVec μ (unitVec u - unitVec v)) X ≤ 0) := by sorry

end FasterSFM
