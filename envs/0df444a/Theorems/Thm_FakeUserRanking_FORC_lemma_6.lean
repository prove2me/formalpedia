-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_6
-- name    : FakeUserRanking.FORC.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:40.754983+00:00
-- url     : https://prove2.me/theorems/f6457d53-25e4-4799-8a16-6d4274599239
-- title:
--   Lemma 6, p. 29 — the good event G of Definition 1 has probability at least 1 − δ, δ = 1/(n³T)
-- statement:
--   Throughout, $n\ge1$ products with click probabilities $\mu_1>\mu_2>\dots>\mu_n$ in $[0,1]$ (condition (1)) and exit probabilities $q_1,\dots,q_{n-1}\in[0,1]$ are shown to $T\ge2$ users, at most $F$ of whom are fake, controlled by an adaptive randomized policy $\mathbf P$ that sees only the past history $\mathcal H_{t-1}$ and puts no mass on fake users once $F$ rounds were fake. FORC (Algorithm 3) runs $L=\lceil\log_2T\rceil$ levels with $\delta=1/(n^3T)$; it does not know $F$, $\mu$ or $q$. Its unspecified choices (tie-breaking in GraphRankSelect, the "arbitrary ranking", and Step 6 when no level qualifies) are arbitrary functions of its past, and the statement holds for all of them.
--
--   **Lemma 6 (Lower Bounding $\mathbb P(\mathcal G)$).** The probability of the event $\mathcal G$ of Definition 1 is at least $1-\delta$, where $\delta=1/(n^3T)$:
--   $$\mathbb P(\mathcal G)\ge1-\delta .$$
--   Here $\mathcal G=\mathcal G_1\cap\mathcal G_2$: $\mathcal G_1$ says that at the end of every round $t\in[T]$, for every level $\ell\ge\ell^\star=\lceil\log_2F\rceil$ and every product $i$, $\hat r^{(\ell)}_{i,t}-w^{(\ell)}_{i,t}\le\mu_i\le\hat r^{(\ell)}_{i,t}+w^{(\ell)}_{i,t}$ with the window $w$ of (21); $\mathcal G_2$ says that every level $\ell\ge\ell^\star$ is exposed to at most $\log(2L/\delta)+3$ fake users.
--
--   On $\mathcal G$ the high levels' graphs contain only correct edges (Lemma 15), which drives the regret bound on $\mathcal G$; the complement contributes at most $1/n^2$ (Lemma 9).
--
--   **Formalization Note.** Products, positions, levels and rounds are 0-based in Lean (`Fin n`, `Fin L`, `Fin T`): Lean product $i$ is paper product $i+1$, and Lean level $k$ is paper level $\ell=k+1$, so the paper's condition $\ell\ge\ell^\star=\lceil\log_2 F\rceil$ is written $F\le 2^{k+1}$. $\mathcal G$ is the definition `goodEvent` (file `Def_FakeUserRanking_FORC_GoodEvent`), a predicate on trajectories.
--
--   Differences from the source:
--   - encoding: products, positions, levels and rounds indexed from 1; paper level ℓ; ℓ ≥ ℓ⋆ = ⌈log₂F⌉ → Fin n, Fin L, Fin T, all 0-based; Lean level k is paper level ℓ = k + 1; ℓ ≥ ⌈log₂F⌉ is written F ≤ 2^(k+1); reason: Lean convention; same instances (F ≤ 2^ℓ is exactly ℓ ≥ ⌈log₂F⌉, and holds for every level when F = 0)
--   - encoding: expectations and probabilities over the random history H_T → finite sums over trajectories Fin T → Step, weighted by the product of the level weights, the policy's PMF and the real customer's cascade law; reason: every space of the model is finite, so this is the law of the history exactly
--   - reading: L = log₂(T) levels → L = ⌈log₂T⌉ (Nat.clog 2 T); reason: the number of levels must be an integer; the ceiling keeps 2^L ≥ T (paper.md Slip 1)
--   - reading: Step 8, no click at the last examined position: r ← r(η − 1)/(η + 1) → r^(ℓ)_i = (clicks of i at level ℓ)/η^(ℓ)_i, the average reward; reason: Step 3 calls r the average reward; FAR's Step 6 has r(η − 1)/η and the proofs use r·η = sum of samples (paper.md Slip 2)
--   - encoding: Step 9 updates η̂, r̂ incrementally, only for levels ℓ ≥ ℓ_t and examined products → η̂, r̂ in closed form (17)–(18) from the current counts, for every level; reason: η^(g) with g ≤ ℓ changes only in rounds with ℓ_t ≤ ℓ, which trigger the update, so the stored values always equal the closed form
--   - reading: ties among the smallest η in GraphRankSelect, its 'arbitrary ranking' on a cyclic graph, and Step 6 when no non-eliminated level above ℓ_t exists are left unspecified → universally quantified functions tb (a member of the tied set) and fb of FORC's past and the sampled level; reason: the claim is made for the algorithm as printed, so it must hold for every resolution of its unspecified choices (paper.md Slip 8)
--   - encoding: n ≥ 1 products and T rounds, unrestricted → 1 ≤ n and 2 ≤ T; reason: δ = 1/(n³T) is undefined at n = 0, and T ≤ 1 gives L = ⌈log₂T⌉ = 0 levels, where FORC draws no level and the statement is vacuous
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 29, Lemma 6 and Definition 1; (21)–(22) p. 28; proof App. D.3, pp. 53–56

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

/-- Lemma 6 (Lower Bounding P(G)), p. 29: `P(G) ≥ 1 − δ` with `δ = 1/(n³T)`. -/
theorem lemma_6 (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)) :
    1 - delta n T ≤ prob inst P (forc n T tb fb) T (goodEvent inst F tb fb) := by sorry

end FakeUserRanking.FORC
