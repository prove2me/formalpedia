-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_Supplement_lemma_3
-- name    : FakeUserRanking.FORC.Supplement.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:34:58.164095+00:00
-- url     : https://prove2.me/theorems/dba72ae7-5b46-4322-89f2-54f5ec1e77fa
-- title:
--   Lemma 3, p. 22 — on E, FAR's graph has no incorrect edge (j, i) and holds (i, j) once η_i, η_j ≥ γ_{j,i}
-- statement:
--   **Lemma 3 (properties of the graph $G$ under event $\mathcal E$).** Let $n,T\ge1$, let $\mu_1>\mu_2>\dots>\mu_n$, and consider any run of FAR on which the event $\mathcal E$ of (8)–(9) holds. Then for any two products $i,j$ with $i>j$:
--
--   1. in any round $t$, the product-ordering graph $G$ does not contain the incorrect edge $(j,i)$;
--   2. if at the end of round $t$
--   $$\eta_{i,t}\ge\gamma_{j,i}\quad\text{and}\quad\eta_{j,t}\ge\gamma_{j,i},$$
--   with $\gamma_{j,i}=\max\{64\log(2nT/\delta)/\Delta_{j,i}^2,\;8F/\Delta_{j,i}\}$ of (13) and $\delta=1/(nT)$, then $G$ contains the correct edge $(i,j)$ in every round $t'\ge t$.
--
--   On $\mathcal E$ the graph thus records only true comparisons, and every comparison once enough feedback on both products has arrived. Lemma 4 and the proof of Theorem 2 rely on both facts.
--
--   **Formalization Note** Products and positions are indexed from $0$ in Lean: Lean product $i$ is the paper's product $i+1$, and likewise for positions. Lean round index $t$ is the paper's round $t+1$; "the end of round $t$" is the state after the first $t$ rounds, $t=0$ being the initial state. In Lean the better product has the smaller index, so the paper's $i>j$ is `j < i`. The statement is pathwise: it holds for every trajectory satisfying $\mathcal E$, the graph "in round $t$" being FAR's graph after the first $t$ rounds. The counts compared with $\gamma_{j,i}$ are FAR's raw feedback counts.
--
--   Differences from the source:
--   - encoding: products, positions and rounds are numbered from 1 → products and positions are `Fin n` and rounds are trajectory indices, all numbered from 0; reason: a relabelling; every instance of the paper corresponds to exactly one Lean instance
--   - generalization: "assume that the event E holds" (a statement about the random run) → every trajectory satisfying E, including trajectories outside a feasible policy’s support; reason: The graph and ranking conclusions use only the deterministic update rules and E; no budget or positive-probability hypothesis is needed. Every source run is included.
--   - generalization: rounds t ∈ [T], FAR with Algorithm 2's tie-break → also t = 0 (the initial, empty graph), and every pair of functions tb, fb; reason: at t = 0 clause 1 holds trivially and clause 2 is vacuous since γ_{j,i} > 0; the graph's edges do not depend on the ranking rule beyond the observations, so FAR proper is a special case
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 22, Lemma 3; γ_{j,i} (13), p. 22; event E, (8)–(9), pp. 20–21; proof in Appendix C.3, p. 50

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_Supplement_FAR
import Definitions.Def_FakeUserRanking_FORC_Supplement_EventE
import Definitions.Def_FakeUserRanking_FORC_Supplement_Gamma

namespace FakeUserRanking.FORC.Supplement

/-- Lemma 3 (Properties of the Graph G under Event E), p. 22, pathwise: on every trajectory in
`E`, for products `j < i` (paper: `i > j`, so `μ_j > μ_i`), (1) FAR's graph never holds the
incorrect edge `(j, i)`, and (2) once `η_{i,t}, η_{j,t} ≥ γ_{j,i}` at the end of round `t`, the
graph holds the correct edge `(i, j)` at the end of every round `t' ≥ t`. -/
theorem lemma_3 (n T F : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n 1) (hE : eventE inst T F tb fb τ) (j i : Fin n) (hji : j < i) :
    (∀ t : ℕ, t ≤ T → (j, i) ∉ (farStateAt n T F tb fb τ t).graph) ∧
    (∀ t : ℕ, t ≤ T →
      gamma13 T F inst j i ≤ ((farStateAt n T F tb fb τ t).cnt i : ℝ) →
      gamma13 T F inst j i ≤ ((farStateAt n T F tb fb τ t).cnt j : ℝ) →
      ∀ t' : ℕ, t ≤ t' → t' ≤ T → (i, j) ∈ (farStateAt n T F tb fb τ t').graph) := by sorry

end FakeUserRanking.FORC.Supplement
