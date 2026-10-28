-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_lemma_11
-- name    : FakeUserRanking.FORC.lemma_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:44.538401+00:00
-- url     : https://prove2.me/theorems/e3bb5b27-cc49-47b1-8d16-530600be4e44
-- title:
--   Lemma 11, p. 51 — for any δ ∈ (0,1), one level ℓ ≥ log₂F sees at most log(2L/δ) + 3 fake users with probability at least 1 − δ/(2L)
-- statement:
--   Throughout, $n\ge1$ products with click probabilities $\mu_1>\mu_2>\dots>\mu_n$ in $[0,1]$ (condition (1)) and exit probabilities $q_1,\dots,q_{n-1}\in[0,1]$ are shown to $T\ge2$ users, at most $F$ of whom are fake, controlled by an adaptive randomized policy $\mathbf P$ that sees only the past history $\mathcal H_{t-1}$ and puts no mass on fake users once $F$ rounds were fake. FORC (Algorithm 3) runs $L=\lceil\log_2T\rceil$ levels with $\delta=1/(n^3T)$; it does not know $F$, $\mu$ or $q$. Its unspecified choices (tie-breaking in GraphRankSelect, the "arbitrary ranking", and Step 6 when no level qualifies) are arbitrary functions of its past, and the statement holds for all of them.
--
--   **Lemma 11.** For any policy $\mathbf P$ with fakeness budget $F$, any $\delta\in(0,1)$ and any fixed level $\ell\ge\log_2(F)$, with probability at least $1-\delta/(2L)$ level $\ell$ is exposed to at most $\log(2L/\delta)+3$ fake users:
--   $$\Pr\Big[\#\{t\le T:\ \ell_t=\ell,\ f_t=1\}\le\log\big(\tfrac{2L}{\delta}\big)+3\Big]\ge1-\frac{\delta}{2L},\qquad L=\lceil\log_2T\rceil .$$
--   Here $\delta$ is an arbitrary number in $(0,1)$, not FORC's parameter.
--
--   Because level $\ell$ is sampled with probability $2^{-\ell}$ independently of the fake entity's decision in the same round, a level $\ell\ge\log_2F$ expects at most one fake user; the lemma is the corresponding high-probability bound. Its union bound over levels is Lemma 5.
--
--   **Formalization Note.** Products, positions, levels and rounds are 0-based in Lean (`Fin n`, `Fin L`, `Fin T`): Lean product $i$ is paper product $i+1$, and Lean level $k$ is paper level $\ell=k+1$, so the paper's condition $\ell\ge\ell^\star=\lceil\log_2 F\rceil$ is written $F\le 2^{k+1}$. The exposure counts rounds whose *sampled* level is $\ell$ and whose user is fake, even when another level's graph ranks (p. 52). "With probability $1-\delta/(2L)$" is read as "at least".
--
--   Differences from the source:
--   - encoding: products, positions, levels and rounds indexed from 1; paper level ℓ; ℓ ≥ ℓ⋆ = ⌈log₂F⌉ → Fin n, Fin L, Fin T, all 0-based; Lean level k is paper level ℓ = k + 1; ℓ ≥ ⌈log₂F⌉ is written F ≤ 2^(k+1); reason: Lean convention; same instances (F ≤ 2^ℓ is exactly ℓ ≥ ⌈log₂F⌉, and holds for every level when F = 0)
--   - encoding: expectations and probabilities over the random history H_T → finite sums over trajectories Fin T → Step, weighted by the product of the level weights, the policy's PMF and the real customer's cascade law; reason: every space of the model is finite, so this is the law of the history exactly
--   - reading: L = log₂(T) levels → L = ⌈log₂T⌉ (Nat.clog 2 T); reason: the number of levels must be an integer; the ceiling keeps 2^L ≥ T (paper.md Slip 1)
--   - reading: Step 8, no click at the last examined position: r ← r(η − 1)/(η + 1) → r^(ℓ)_i = (clicks of i at level ℓ)/η^(ℓ)_i, the average reward; reason: Step 3 calls r the average reward; FAR's Step 6 has r(η − 1)/η and the proofs use r·η = sum of samples (paper.md Slip 2)
--   - encoding: Step 9 updates η̂, r̂ incrementally, only for levels ℓ ≥ ℓ_t and examined products → η̂, r̂ in closed form (17)–(18) from the current counts, for every level; reason: η^(g) with g ≤ ℓ changes only in rounds with ℓ_t ≤ ℓ, which trigger the update, so the stored values always equal the closed form
--   - reading: ties among the smallest η in GraphRankSelect, its 'arbitrary ranking' on a cyclic graph, and Step 6 when no non-eliminated level above ℓ_t exists are left unspecified → universally quantified functions tb (a member of the tied set) and fb of FORC's past and the sampled level; reason: the claim is made for the algorithm as printed, so it must hold for every resolution of its unspecified choices (paper.md Slip 8)
--   - encoding: n ≥ 1 products and T rounds, unrestricted → 1 ≤ n and 2 ≤ T; reason: δ = 1/(n³T) is undefined at n = 0, and T ≤ 1 gives L = ⌈log₂T⌉ = 0 levels, where FORC draws no level and the statement is vacuous
--   - reading: with probability 1 − δ/(2L) → probability at least 1 − δ/(2L); reason: a probability bound; the proof (p. 52) gives a lower bound
--   - reading: any level ℓ ≥ log₂(F) is exposed to at most log(2L/δ) + 3 fake users → for each fixed level k with F ≤ 2^(k+1), the bound holds with that probability; reason: the proof fixes one level ('for a fixed level', p. 51) and Lemma 5 is its union bound (paper.md Slip 12)
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 51, Lemma 11; proof pp. 51–52, App. D.1

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

/-- Lemma 11, p. 51: one level `ℓ ≥ log₂ F` (Lean: `F ≤ 2^(k+1)`) is exposed to at most
`log(2L/δ) + 3` fake users with probability at least `1 − δ/(2L)`, for any `δ ∈ (0,1)`. -/
theorem lemma_11 (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    1 - δ / (2 * (numLevels T : ℝ)) ≤
      prob inst P (forc n T tb fb) T
        (fun τ => (exposure k τ : ℝ) ≤ Real.log (2 * (numLevels T : ℝ) / δ) + 3) := by sorry

end FakeUserRanking.FORC
