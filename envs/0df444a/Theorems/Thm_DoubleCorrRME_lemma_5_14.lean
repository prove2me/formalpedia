-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_5_14
-- name    : DoubleCorrRME.lemma_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:38.341585+00:00
-- url     : https://prove2.me/theorems/5211c381-ecc6-43de-b81b-fb03466e2e8a
-- title:
--   Lemma 5.14, p.40 — weight preservation: $\|u^{(t)}\|_1\ge1-O(\varepsilon)$, $\|\mathrm{vec}(p^{(t)})\|_1\ge(1-O(\alpha'))\|u^{(t)}\|_1$
-- statement:
--   In the context of Lemma 5.6, for every round $t$ of the sample-level filter (Algorithm 3 with successful approximations),
--
--   1. $\|u^{(t)}\|_1\ge1-C\varepsilon$, and
--   2. $\|\mathrm{vec}(p^{(t)})\|_1\ge(1-C\alpha')\|u^{(t)}\|_1$,
--
--   for a universal constant $C$, when $\varepsilon$ is sufficiently small and $C_Q$ sufficiently large.
--
--   The filter thus keeps almost all user weight and almost all sample weight within surviving users, so the weighted batch means stay close to the truncated reference.
--
--   **Formalization Note** The rounds are $t\le KT$ for every trajectory with $K$ completed epochs, including the output round. Nothing about $\|\mathrm{vec}(p)\|_1$ is assumed.
--
--   Differences from the source:
--   - generalization: the universal constants C_ref, C_∆ of §4.1 (and K₀, K₁, C_Q) fixed once → ∀ C_ref, C_∆ > 0, then ∃ thresholds for K₀, K₁, C_Q; later constants may depend on earlier ones; reason: the statement holds for every choice of the §4.1 constants, so it specializes to the paper's fixed choice; every constant is still independent of N, n, d, ε, α, δ and the data
--   - reading: ∆ := O(√α′) (§4.1) and ∆ ← C_∆(√(d/m) + √α′ + √(L/m)) (Algorithm 2, line 2) → ∆ = C_∆√α′, κ = 1 + ∆²/α′; reason: §4.1 is the notation of §§4–5; since d/m, L/m ≤ α′/C_ref the two forms agree up to a change of C_∆, which is universally quantified
--   - reading: the lemma lives on the event of Lemma 4.1 for the corrupted data of Definition 1.1, under Remark 5.4's "we assume ε > 10K₁α′ throughout" and §4.1's δ ∈ (0, 0.1) → explicit hypotheses IsContext (|B| ≤ εN, at most αNn changed points outside B, |ℐ| ≥ (1 − α′)Nn, (α′, ∆)-stability of {z_k : k ∈ ℐ} w.r.t. (µ, I_d), δ ∈ (0, 1/10)) and 10K₁α′ < ε; reason: these are the standing assumptions of §5.2; the lemma is deterministic given them
--   - encoding: N users, n samples per user in ℝ^d → 1 ≤ N, 1 ≤ n, 1 ≤ d; reason: excludes only the empty settings, where the averages divide by 0
--   - reading: the sample-level filter (Algorithm 3) "conditioned on successful power-method and QUE-score approximations" → any trajectory satisfying IsStage1Prefix / IsStage1Run: ν = 1/40, Λ̂_k a ν-approximation of ∥M_s(u^(kT), w^(kT))∥₂, each τ̃^(t) a ν-approximate QUE score matrix for the epoch's MMW density, capped updates at their stopping time; reason: the randomized subroutines are replaced by their success guarantees, exactly as the lemma conditions on them
--   - encoding: for all t ∈ 𝒯, two O(·) → for every t ≤ KT of every K-epoch trajectory; one constant C for both, ∃ C before C_Q and c; reason: 𝒯 is the set of QUE rounds; the proof fixes C first and then takes C_Q large and ε small
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 5.14, p.40 (PDF p.41)

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Stability
import Definitions.Def_DoubleCorrRME_Params
import Definitions.Def_DoubleCorrRME_Weights
import Definitions.Def_DoubleCorrRME_Filter

namespace DoubleCorrRME

/-- **Lemma 5.14** (weight preservation), p.40 (PDF p.41).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Lemma 5.14. For all t ∈ 𝒯, we have
• Part 1. ∥u^(t)∥₁ ≥ 1 − O(ε), and
• Part 2. ∥vec(p^(t))∥₁ ≥ (1 − O(α′))∥u^(t)∥₁."

**Formalization Note.**
* **Constants.** For every choice of the §4.1 constants `C_ref, C_∆ > 0` (Lemma 4.1 fixes one),
  `K₀` is a sufficiently large universal constant (Definition 5.2), `K₁ ≥ 2K₀` a sufficiently large
  one (Definition 5.3), `C_Q` a sufficiently large one (Lemma 5.6), and "for sufficiently small ε" is
  `ε < c`; every `O(·)` is one constant `C`. Each later constant may depend on the earlier ones and
  on nothing else (not on `N, n, d, ε, α, δ` or the data).
* **Context** (`IsContext`, see `Def_DoubleCorrRME_Filter`): one realization `(z, x, B, ℐ, µ)` with
  the corruption guarantee of Definition 1.1, `|ℐ| ≥ (1 − α′)Nn`, the `(α′, ∆)`-stability of
  `{z_k : k ∈ ℐ}` with respect to `(µ, I_d)` (Lemma 4.1, Part 1), `δ ∈ (0, 0.1)`, and the standing
  assumption `ε > 10K₁α′` of Remark 5.4 ("we assume ε > 10K₁α′ throughout the following analysis").
  `α′, ∆, κ` are those of §4.1 (`alphaP`, `deltaP`, `kappaP`); `𝒢, D_i, ℛ, θ₀, θ₁` are defined from
  the context. `N, n, d ≥ 1`.
* 𝒯, the QUE rounds of the sample-level filter: every round `t ≤ KT` of every trajectory of
  Algorithm 3 with successful approximations that has completed `K` epochs (`IsStage1Prefix`),
  including the final round `KT` whose weights are the filter's output. Nothing is assumed about
  `∥vec(p^(t))∥₁`: the lemma proves it.
* One constant `C` serves both `O(·)`s; it is chosen before `C_Q` (the proof fixes it first and then
  takes `C_Q` large and `ε` small depending on it). -/
theorem lemma_5_14 :
    ∀ Cref CΔ : ℝ, 0 < Cref → 0 < CΔ →
    ∃ K0min : ℝ, 0 < K0min ∧ ∀ K0 : ℝ, K0min ≤ K0 →
    ∃ K1min : ℝ, ∀ K1 : ℝ, K1min ≤ K1 → 2 * K0 ≤ K1 →
    ∃ C : ℝ, 0 < C ∧ ∃ CQmin : ℝ, ∀ CQ : ℝ, CQmin ≤ CQ → ∃ c : ℝ, 0 < c ∧
    ∀ (N n d : ℕ), 1 ≤ N → 1 ≤ n → 1 ≤ d →
    ∀ (ε α δ : ℝ) (z x : Fin N → Fin n → Vec d) (B : Finset (Fin N))
      (I : Finset (Fin N × Fin n)) (μ : Vec d),
      IsContext Cref CΔ ε α δ z x B I μ → ε < c →
      let α' := alphaP Cref N n d α δ
      let κ := kappaP α' (deltaP CΔ α')
      10 * K1 * α' < ε →
      ∀ (tr : Stage1Traj N n) (K : ℕ), IsStage1Prefix x ε α' κ CQ K1 tr K →
        ∀ t ≤ K * epochLen d,
          1 - C * ε ≤ l1U (tr.u t) ∧
            (1 - C * α') * l1U (tr.u t) ≤ l1P (prodW (tr.u t) (tr.w t)) := by sorry

end DoubleCorrRME
