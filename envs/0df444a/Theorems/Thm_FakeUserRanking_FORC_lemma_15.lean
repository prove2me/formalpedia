-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_15
-- name    : FakeUserRanking.FORC.lemma_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:52.811793+00:00
-- url     : https://prove2.me/theorems/d56679c3-c44b-4ef9-bc1b-ba70fe17ff56
-- title:
--   Lemma 15, p. 57 — on G, levels ℓ ≥ ℓ⋆ never hold an incorrect edge and hold edge (i, j) once η̂_i, η̂_j ≥ γ_{j,i}
-- statement:
--   Throughout, $n\ge1$ products with click probabilities $\mu_1>\mu_2>\dots>\mu_n$ in $[0,1]$ (condition (1)) and exit probabilities $q_1,\dots,q_{n-1}\in[0,1]$ are shown to $T\ge2$ users, at most $F$ of whom are fake, controlled by an adaptive randomized policy $\mathbf P$ that sees only the past history $\mathcal H_{t-1}$ and puts no mass on fake users once $F$ rounds were fake. FORC (Algorithm 3) runs $L=\lceil\log_2T\rceil$ levels with $\delta=1/(n^3T)$; it does not know $F$, $\mu$ or $q$. Its unspecified choices (tie-breaking in GraphRankSelect, the "arbitrary ranking", and Step 6 when no level qualifies) are arbitrary functions of its past, and the statement holds for all of them.
--
--   **Lemma 15 (Properties of Graph $G$ under Event $\mathcal G$).** Assume that the event $\mathcal G$ of Definition 1 holds. Then for any two products $i,j$ with $i>j$ (so $\mu_j>\mu_i$) and any level $\ell\ge\ell^\star=\lceil\log_2F\rceil$:
--   1. at the end of every round $t$, the graph $G^{(\ell)}$ does not contain the incorrect edge $(j,i)$;
--   2. if at the end of round $t$
--   $$\hat\eta^{(\ell)}_{i,t}\ge\gamma_{j,i}\quad\text{and}\quad\hat\eta^{(\ell)}_{j,t}\ge\gamma_{j,i},\qquad\gamma_{j,i}=\frac{64\log(4nT/\delta)}{\Delta_{j,i}^2},$$
--   then $G^{(\ell)}$ contains the correct edge $(i,j)$ at the end of every round $t'\ge t$.
--
--   The statement is pathwise: it holds on every realization in $\mathcal G$. It shows that the high levels are never eliminated and learn every pair once both products have enough cross-learned feedback; it is the basis of Lemmas 7 and 10.
--
--   **Formalization Note.** Products, positions, levels and rounds are 0-based in Lean (`Fin n`, `Fin L`, `Fin T`): Lean product $i$ is paper product $i+1$, and Lean level $k$ is paper level $\ell=k+1$, so the paper's condition $\ell\ge\ell^\star=\lceil\log_2 F\rceil$ is written $F\le 2^{k+1}$. "Round $t$" means FORC's state after the first $t$ rounds (Steps 8–11 included); clause 1 holds for $t=0,\dots,T$ and clause 2 for $1\le t\le t'\le T$. `j < i` in `Fin n` is the paper's $i>j$.
--
--   Differences from the source:
--   - encoding: products, positions, levels and rounds indexed from 1; paper level ℓ; ℓ ≥ ℓ⋆ = ⌈log₂F⌉ → Fin n, Fin L, Fin T, all 0-based; Lean level k is paper level ℓ = k + 1; ℓ ≥ ⌈log₂F⌉ is written F ≤ 2^(k+1); reason: Lean convention; same instances (F ≤ 2^ℓ is exactly ℓ ≥ ⌈log₂F⌉, and holds for every level when F = 0)
--   - encoding: expectations and probabilities over the random history H_T → finite sums over trajectories Fin T → Step, weighted by the product of the level weights, the policy's PMF and the real customer's cascade law; reason: every space of the model is finite, so this is the law of the history exactly
--   - reading: L = log₂(T) levels → L = ⌈log₂T⌉ (Nat.clog 2 T); reason: the number of levels must be an integer; the ceiling keeps 2^L ≥ T (paper.md Slip 1)
--   - reading: Step 8, no click at the last examined position: r ← r(η − 1)/(η + 1) → r^(ℓ)_i = (clicks of i at level ℓ)/η^(ℓ)_i, the average reward; reason: Step 3 calls r the average reward; FAR's Step 6 has r(η − 1)/η and the proofs use r·η = sum of samples (paper.md Slip 2)
--   - encoding: Step 9 updates η̂, r̂ incrementally, only for levels ℓ ≥ ℓ_t and examined products → η̂, r̂ in closed form (17)–(18) from the current counts, for every level; reason: η^(g) with g ≤ ℓ changes only in rounds with ℓ_t ≤ ℓ, which trigger the update, so the stored values always equal the closed form
--   - reading: ties among the smallest η in GraphRankSelect, its 'arbitrary ranking' on a cyclic graph, and Step 6 when no non-eliminated level above ℓ_t exists are left unspecified → universally quantified functions tb (a member of the tied set) and fb of FORC's past and the sampled level; reason: the claim is made for the algorithm as printed, so it must hold for every resolution of its unspecified choices (paper.md Slip 8)
--   - encoding: n ≥ 1 products and T rounds, unrestricted → 1 ≤ n and 2 ≤ T; reason: δ = 1/(n³T) is undefined at n = 0, and T ≤ 1 gives L = ⌈log₂T⌉ = 0 levels, where FORC draws no level and the statement is vacuous
--   - encoding: 'Assume that event G holds … in any round t' → for every trajectory in goodEvent; round t is FORC's state after t rounds, t ≤ T (clause 1), 1 ≤ t ≤ t' ≤ T (clause 2); reason: the lemma is a deterministic consequence of G; the horizon has rounds 1..T
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 57, Lemma 15; (23) p. 29

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

/-- Lemma 15 (Properties of Graph G under Event G), p. 57, pathwise: on every trajectory in the
good event, for products `j < i` (paper: `i > j`, so `μ_j > μ_i`) and every level `ℓ ≥ ℓ⋆`
(Lean: `F ≤ 2^(k+1)`), (1) `G^(ℓ)` never holds the incorrect edge `(j, i)`, and (2) once
`η̂^(ℓ)_{i,t}, η̂^(ℓ)_{j,t} ≥ γ_{j,i}` at the end of round `t`, `G^(ℓ)` holds the edge `(i, j)` at the
end of every round `t' ≥ t`. -/
theorem lemma_15 (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (hG : goodEvent inst F tb fb τ)
    (j i : Fin n) (hji : j < i) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    (∀ t : ℕ, t ≤ T → (j, i) ∉ (stateAt tb fb τ t).graph k) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ T →
      gamma T inst j i ≤ etaHat (stateAt tb fb τ t) k i →
      gamma T inst j i ≤ etaHat (stateAt tb fb τ t) k j →
      ∀ t' : ℕ, t ≤ t' → t' ≤ T → (i, j) ∈ (stateAt tb fb τ t').graph k) := by sorry

end FakeUserRanking.FORC
