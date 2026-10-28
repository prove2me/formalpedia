-- Prove2me | Theorems.Thm_FakeUserRanking_FORC_theorem_3
-- name    : FakeUserRanking.FORC.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:49.691426+00:00
-- url     : https://prove2.me/theorems/ef4bf091-be66-4ed0-b237-458faa2b7ca9
-- title:
--   Theorem 3, p. 26 — with F unknown, FORC's regret is O((n²F + log T) Σ_{j<i} log(nT)/Δ_{j,i}) (corrected: T ≥ 2)
-- statement:
--   **Theorem 3 (Unknown Fakeness Budget: Regret of FORC Algorithm).** Let $F$ be the fakeness budget and assume that $F$ is unknown to the platform. Then the expected regret of the FORC algorithm satisfies
--   $$\mathrm{Reg}_T=O\Big(\big(n^2F+\log T\big)\sum_{j=1}^n\sum_{i=j+1}^n\frac{\log(nT)}{\Delta_{j,i}}\Big)\qquad(16).$$
--
--   Precisely: there is an absolute constant $C$ such that for all $n\ge1$, $T\ge2$, $F\ge0$, every instance with click probabilities $\mu_1>\dots>\mu_n$ in $[0,1]$ and exit probabilities in $[0,1]$, every adaptive randomized fake-user policy $\mathbf P$ with fakeness budget $F$, and every resolution of FORC's unspecified choices,
--   $$\mathbb E_{\mathcal H_T(\pi^\star)}\Big[\sum_{t=1}^T\mathcal C_{r,t}(\pi^\star)\Big]-\mathbb E_{\mathcal H_T(\pi_t)}\Big[\sum_{t=1}^T\mathcal C_{r,t}(\pi_t)\Big]\le C\,\big(n^2F+\log T\big)\sum_{j=1}^n\sum_{i=j+1}^n\frac{\log(nT)}{\mu_j-\mu_i},$$
--   where $\pi_t$ are FORC's rankings (Algorithm 3, with $L=\lceil\log_2T\rceil$ levels and $\delta=1/(n^3T)$), $\pi^\star(i)=i$, and both runs face the same policy. FORC uses neither $F$ nor the click or exit probabilities.
--
--   This is the paper's central result: without knowing how many users are fake, the platform's regret grows only linearly in $F$ and logarithmically in $T$, compared with the $\Omega(T)$ regret of UCB with $F=O(\log^2T)$ fake users (Theorem 1).
--
--   **Formalization Note.** Products are `Fin n` (0-based); `Finset.Ioi j` is $\{i:i>j\}$. Regret is defined for a fixed policy as a finite sum over trajectories; the supremum over policies in (2) is the quantification over every policy within budget. The constant $C$ is chosen before $n$, $T$, $F$, the instance, the policy and FORC's choices. The hypothesis $T\ge2$ is a correction: the bound fails at $T=1$.
--
--   Differences from the source:
--   - encoding: products, positions, levels and rounds indexed from 1; paper level ℓ; ℓ ≥ ℓ⋆ = ⌈log₂F⌉ → Fin n, Fin L, Fin T, all 0-based; Lean level k is paper level ℓ = k + 1; ℓ ≥ ⌈log₂F⌉ is written F ≤ 2^(k+1); reason: Lean convention; same instances (F ≤ 2^ℓ is exactly ℓ ≥ ⌈log₂F⌉, and holds for every level when F = 0)
--   - encoding: expectations and probabilities over the random history H_T → finite sums over trajectories Fin T → Step, weighted by the product of the level weights, the policy's PMF and the real customer's cascade law; reason: every space of the model is finite, so this is the law of the history exactly
--   - reading: L = log₂(T) levels → L = ⌈log₂T⌉ (Nat.clog 2 T); reason: the number of levels must be an integer; the ceiling keeps 2^L ≥ T (paper.md Slip 1)
--   - reading: Step 8, no click at the last examined position: r ← r(η − 1)/(η + 1) → r^(ℓ)_i = (clicks of i at level ℓ)/η^(ℓ)_i, the average reward; reason: Step 3 calls r the average reward; FAR's Step 6 has r(η − 1)/η and the proofs use r·η = sum of samples (paper.md Slip 2)
--   - encoding: Step 9 updates η̂, r̂ incrementally, only for levels ℓ ≥ ℓ_t and examined products → η̂, r̂ in closed form (17)–(18) from the current counts, for every level; reason: η^(g) with g ≤ ℓ changes only in rounds with ℓ_t ≤ ℓ, which trigger the update, so the stored values always equal the closed form
--   - reading: ties among the smallest η in GraphRankSelect, its 'arbitrary ranking' on a cyclic graph, and Step 6 when no non-eliminated level above ℓ_t exists are left unspecified → universally quantified functions tb (a member of the tied set) and fb of FORC's past and the sampled level; reason: the claim is made for the algorithm as printed, so it must hold for every resolution of its unspecified choices (paper.md Slip 8)
--   - encoding: n ≥ 1 arbitrary → 1 ≤ n; reason: δ = 1/(n³T) is undefined at n = 0
--   - correction: T arbitrary → 2 ≤ T; reason: at T = 1 the bound is C(n²F + log 1)Σ log(n)/Δ = 0 for F = 0, but with n = 2, μ = (1, 1/2), q₁ = 1, F = 0 and a tie-break putting product 2 first, Reg₁ = 1/2 > 0 (paper.md Slip 1)
--   - reading: Reg_T = O(·) → ∃ C : ℝ placed before n, T, F, the instance, the policy and FORC's choices; reason: O(·) with one absolute constant, uniform over everything the bound is stated for
--   - encoding: Reg_T = sup over feasible policies P of the regret difference (2) → the bound for every policy P with WithinBudget F P; reason: a bound for every policy is a bound on the supremum, with the same constant (paper.md Slip 13)
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, p. 26, Theorem 3, (16); regret (2) p. 12; proof pp. 28–34 and App. D

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm

namespace FakeUserRanking.FORC

/-- Theorem 3 (Unknown Fakeness Budget: Regret of FORC Algorithm), p. 26: there is an absolute
constant `C` such that for every instance, every fakeness budget `F` (unknown to FORC), every
fake-user policy within budget `F` and every resolution of FORC's unspecified choices,
`Reg_T ≤ C (n²F + log T) ∑_{j<i} log(nT)/Δ_{j,i}`. -/
theorem theorem_3 :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
        regret inst P (forc n T tb fb) T ≤
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i) := by sorry

end FakeUserRanking.FORC
