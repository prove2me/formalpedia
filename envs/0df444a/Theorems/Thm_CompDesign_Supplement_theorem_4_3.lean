-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_4_3
-- name    : CompDesign.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:53:45.37853+00:00
-- url     : https://prove2.me/theorems/17762798-3b0d-43e9-a34b-ae116f55523b
-- title:
--   Theorem 4.3 — exponential strict better-response paths in $\Gamma^{mc}$, even when $\lambda\ll1$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget and $c_i\ge0$ the private costs. the value function $v$ satisfies Assumption 3.1: $v(\emptyset)=0$, $v$ is monotone and submodular. In the game $\Gamma^{mc}$ induced by the marginal-contribution rule (8), a strict better response moves from $S$ to $S'$ by one agent switching its participation and strictly raising its own utility.
--
--   **Theorem 4.3 (Exponential better-response paths).** There are an absolute constant $\kappa>0$ and $n_0$ such that for every $n\ge n_0$ and every $\bar\lambda>0$ there is an instance of $\Gamma^{mc}$ with $n$ agents, a normalized monotone submodular $v$ and costs
--   $$0\le c_i<B,\qquad c_i\le\bar\lambda B,$$
--   which has a strict better-response path $S_0,S_1,\dots,S_T$ of length $T\ge 2^{\kappa n}$.
--
--   Theorem 4.1 shows that strict better responses of $\Gamma^{mc}$ always terminate; this theorem shows that they may take exponentially many steps, even under an arbitrarily strong large-market condition.
--
--   Differences from the source:
--   - reading: a path of length 2^{Ω(n)} for some instances → ∃ κ > 0, ∃ n₀, ∀ n ≥ n₀: an n-agent instance with a path of T ≥ 2^{κ n} moves; reason: the standard meaning of 2^{Ω(n)} lower bounds; every large n rather than infinitely many n, which is stronger (dummy agents of zero marginal value never move)
--   - reading: "this result holds even when λ = max_i c_i/B ≪ 1" → for every λ̄ > 0, with the same κ and n₀, an instance with c_i ≤ λ̄·B; reason: the proof's path length does not depend on γ = λ, which can be chosen arbitrarily small
--   - encoding: a strict better-response path (from some initial state) → S : ℕ → Finset (Fin n) with IsStrictImprovement v B c (S t) (S (t+1)) for all t < T; reason: the published definition of a strict better response of Γ^mc
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 4.3, §4.3.1, p.23 (PDF 26)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesign_IsStrictImprovement

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 4.3 (Exponential better-response paths), §4.3.1, p.23 (PDF 26) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). There are
instances of `Γ^mc` with a monotone submodular valuation function `v` and `c_i < B` for every
`i ∈ N` for which there exists a strict better-response path (from some initial state) that has
length `2^{Ω(n)}`. In fact, this result holds even when `λ = max_i c_i/B ≪ 1`.

**Formalization Note.** `2^{Ω(n)}` is read as: there are an absolute constant `κ > 0` and `n₀` such
that for every `n ≥ n₀` and every `λ̄ > 0` there is an `n`-agent instance with a path of `T ≥ 2^{κn}`
moves; `κ` and `n₀` do not depend on `λ̄` (the proof's path length does not depend on `γ = λ`). A path
`S_0, …, S_T` is a sequence whose consecutive sets are strict better responses of `Γ^mc`
(`CompDesign.IsStrictImprovement`, the published definition). Assumption 3.1, `B > 0` and `c ≥ 0` are
the standing assumptions. -/
theorem theorem_4_3 :
    ∃ κ : ℝ, 0 < κ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ lbar : ℝ, 0 < lbar →
      ∃ (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ), 0 < B ∧ v ∅ = 0 ∧ IsMonotoneSF v ∧
        IsSubmodularSF v ∧ (∀ i, 0 ≤ c i ∧ c i < B ∧ c i ≤ lbar * B) ∧
        ∃ (T : ℕ) (S : ℕ → Finset (Fin n)), (2 : ℝ) ^ (κ * (n : ℝ)) ≤ (T : ℝ) ∧
          ∀ t, t < T → CompDesign.IsStrictImprovement v B c (S t) (S (t + 1)) := by sorry

end CompDesign.Supplement
