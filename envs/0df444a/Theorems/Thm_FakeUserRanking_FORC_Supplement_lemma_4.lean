-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_Supplement_lemma_4
-- name    : FakeUserRanking.FORC.Supplement.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:35:51.499819+00:00
-- url     : https://prove2.me/theorems/1ac6b92a-635d-49ca-a71e-2c2bec5ecdf5
-- title:
--   Lemma 4, p. 22 — on E, if FAR ranks i above j < i, some k ≤ j lacks the edge (i, k), η_i ≤ η_k and η_i < γ_{k,i}
-- statement:
--   **Lemma 4 (necessary conditions for an incorrect ordering).** Let $n,T\ge1$, let $\mu_1>\mu_2>\dots>\mu_n$, and consider any run of FAR on which the event $\mathcal E$ of (8)–(9) holds. Suppose that in round $t+1\le T$ the ranking $\textsc{GraphRankSelect}(\eta,G)$ (Algorithm 2) places product $i$ at a better position than product $j$, for some $i>j$. Then there is a product $k\le j$ such that
--
--   1. the product-ordering graph $G$ after round $t$ does not contain the edge $(i,k)$;
--   2. $\eta_{i,t}\le\eta_{k,t}$, that is, there is no more feedback on product $i$ than on product $k$;
--   3. $\eta_{i,t}<\gamma_{k,i}$, with $\gamma_{k,i}$ of (13).
--
--   The same $k$ satisfies all three conditions. Any misordering of an inferior product is therefore due to too little feedback on it, which bounds the number of rounds in which a real user examines product $i$ placed at position $j$ by $\lceil\gamma_{j,i}\rceil$ (at most $\gamma_{j,i}+1$) when accounting for integer feedback counts in the proof of Theorem 2.
--
--   **Formalization Note** Products and positions are indexed from $0$ in Lean: Lean product $i$ is the paper's product $i+1$, and likewise for positions. Lean round index $t$ is the paper's round $t+1$; "the end of round $t$" is the state after the first $t$ rounds, $t=0$ being the initial state. In Lean the better product has the smaller index, so the paper's $i>j$ is `j < i`. The Lean round index $t$ is the paper's round $t+1$; the ranking of that round is computed from FAR's state after the first $t$ rounds, and $\eta_{\cdot,t}$, $G$ are that state ($t=0$ is the initial state). "A better position" means a smaller position index. Algorithm 2's tie-break must choose one of the tied candidates with the smallest feedback count, which is the hypothesis on `tb`; the arbitrary ranking `fb` on a cyclic graph is any function of FAR's past.
--
--   Differences from the source:
--   - encoding: products, positions and rounds are numbered from 1 → products and positions are `Fin n` and rounds are trajectory indices, all numbered from 0; reason: a relabelling; every instance of the paper corresponds to exactly one Lean instance
--   - generalization: "assume that the event E holds" (a statement about the random run) → every trajectory satisfying E, including trajectories outside a feasible policy’s support; reason: The graph and ranking conclusions use only the deterministic update rules and E; no budget or positive-probability hypothesis is needed. Every source run is included.
--   - reading: GraphRankSelect chooses "the one with smallest η_i value" among the candidates; ties are left unspecified → tb is any function returning a member of every nonempty tied set; fb is any ranking-valued function; reason: Algorithm 2 fixes only these properties of its choices, so the lemma is stated for every resolution of them
--   - generalization: The statement refers to the state after round t and the ranking in round t + 1 → The initial state t = 0 is also included; reason: At t = 0 the graph is empty and all counts vanish, so choosing k = j gives all three conclusions because γ_{j,i} > 0.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 22, Lemma 4; Algorithm 2, p. 19; γ (13), p. 22; proof in Appendix C.4, p. 51

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_Supplement_FAR
import Definitions.Def_FakeUserRanking_FORC_Supplement_EventE
import Definitions.Def_FakeUserRanking_FORC_Supplement_Gamma

namespace FakeUserRanking.FORC.Supplement

/-- Lemma 4 (Necessary Conditions for an Incorrect Ordering), p. 22, pathwise: on every trajectory
in `E`, if the ranking FAR displays in Lean round `t` (paper round `t + 1`) puts product `i` at a
better position than product `j < i` (paper: `i > j`), then some product `k ≤ j` has (a) no edge
`(i, k)` in the graph after paper round `t`, (b) `η_{i,t} ≤ η_{k,t}` and (c) `η_{i,t} < γ_{k,i}`. -/
theorem lemma_4 (n T F : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (htb : ∀ h S, S.Nonempty → tb h S ∈ S)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n 1) (hE : eventE inst T F tb fb τ)
    (t : Fin T) (j i : Fin n) (hji : j < i)
    (hord : (ranking (far n T F tb fb) τ t).symm i < (ranking (far n T F tb fb) τ t).symm j) :
    ∃ k : Fin n, k ≤ j ∧
      (i, k) ∉ (farStateAt n T F tb fb τ t).graph ∧
      (farStateAt n T F tb fb τ t).cnt i ≤ (farStateAt n T F tb fb τ t).cnt k ∧
      ((farStateAt n T F tb fb τ t).cnt i : ℝ) < gamma13 T F inst k i := by sorry

end FakeUserRanking.FORC.Supplement
