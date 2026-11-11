-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_5_13
-- name    : DoubleCorrRME.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:37.814412+00:00
-- url     : https://prove2.me/theorems/1477d870-fc9f-4af5-b647-86e047fa0e43
-- title:
--   Lemma 5.13, p.39 — soft-loss accounting: $|\bar{\mathcal R}|=O(\varepsilon N)$, $L^{\rm tot}_g\le L^{\rm tot}_b=O(\alpha')$
-- statement:
--   In the context of Lemma 5.6, run the sample-level filter (Algorithm 3) with successful approximations, and suppose that the assumptions of Lemma 5.6 hold at every round where a capped update is performed ($u_i\in\{0,1/N\}$, $w_{i,j}\le1/n$, $\|\mathrm{vec}(p)\|_1\ge1-C_1\varepsilon$). Let $\bar{\mathcal R}=[N]\setminus\mathcal R$. Then
--
--   $$|\bar{\mathcal R}|\le C\varepsilon N\qquad\text{and}\qquad L^{\mathrm{tot}}_g\le L^{\mathrm{tot}}_b\le C\alpha',$$
--
--   where $L^{\mathrm{tot}}_g,L^{\mathrm{tot}}_b$ are the total soft losses on and off the matched regular-good samples (Definitions 5.8, 5.12). The same bound holds for every prefix of the QUE rounds.
--
--   The filter therefore loses $O(\alpha')$ good weight in total, which is what the weight-preservation lemma builds on.
--
--   **Formalization Note** The constant $C$ is chosen before $C_1$ and $C_Q$. Prefixes are the rounds $s<t$ for every $t\le KT$ of a trajectory with $K$ completed epochs.
--
--   Differences from the source:
--   - generalization: the universal constants C_ref, C_∆ of §4.1 (and K₀, K₁, C_Q) fixed once → ∀ C_ref, C_∆ > 0, then ∃ thresholds for K₀, K₁, C_Q; later constants may depend on earlier ones; reason: the statement holds for every choice of the §4.1 constants, so it specializes to the paper's fixed choice; every constant is still independent of N, n, d, ε, α, δ and the data
--   - reading: ∆ := O(√α′) (§4.1) and ∆ ← C_∆(√(d/m) + √α′ + √(L/m)) (Algorithm 2, line 2) → ∆ = C_∆√α′, κ = 1 + ∆²/α′; reason: §4.1 is the notation of §§4–5; since d/m, L/m ≤ α′/C_ref the two forms agree up to a change of C_∆, which is universally quantified
--   - reading: the lemma lives on the event of Lemma 4.1 for the corrupted data of Definition 1.1, under Remark 5.4's "we assume ε > 10K₁α′ throughout" and §4.1's δ ∈ (0, 0.1) → explicit hypotheses IsContext (|B| ≤ εN, at most αNn changed points outside B, |ℐ| ≥ (1 − α′)Nn, (α′, ∆)-stability of {z_k : k ∈ ℐ} w.r.t. (µ, I_d), δ ∈ (0, 1/10)) and 10K₁α′ < ε; reason: these are the standing assumptions of §5.2; the lemma is deterministic given them
--   - encoding: N users, n samples per user in ℝ^d → 1 ≤ N, 1 ≤ n, 1 ≤ d; reason: excludes only the empty settings, where the averages divide by 0
--   - reading: the sample-level filter (Algorithm 3) "conditioned on successful power-method and QUE-score approximations" → any trajectory satisfying IsStage1Prefix / IsStage1Run: ν = 1/40, Λ̂_k a ν-approximation of ∥M_s(u^(kT), w^(kT))∥₂, each τ̃^(t) a ν-approximate QUE score matrix for the epoch's MMW density, capped updates at their stopping time; reason: the randomized subroutines are replaced by their success guarantees, exactly as the lemma conditions on them
--   - encoding: "suppose that the assumptions of Lemma 5.6 hold whenever a capped update is performed" → at every updated round t < KT: u_i ∈ {0, 1/N}, w_{i,j} ≤ 1/n, ∥vec(p)∥₁ ≥ 1 − C₁ε, with ∀ C₁ before C_Q and c; reason: Lemma 5.6's remaining condition σ ≥ C_Qκ holds at every updated round of such a trajectory (σ̃ > Λ̂/10 > 1.6C_Qκ)
--   - encoding: L^tot_b = O(α′) and the order of constants → L^tot_b ≤ Cα′ with ∃ C before C₁, C_Q; reason: = O(·) is an upper bound; the proof's bound uses only Definition 5.2, (12) and Lemma 5.10, and Lemma 5.14 relies on its independence of C₁
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 5.13, p.39 (PDF p.40); Definition 5.12

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Stability
import Definitions.Def_DoubleCorrRME_Params
import Definitions.Def_DoubleCorrRME_Weights
import Definitions.Def_DoubleCorrRME_Filter

namespace DoubleCorrRME

/-- **Lemma 5.13** (soft-loss accounting), p.39 (PDF p.40).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Lemma 5.13. Under Definition 5.12, suppose that the assumptions of Lemma 5.6 hold whenever a capped
update is performed. Let ℛ̄ := [N] \ ℛ Then, we have |ℛ̄| = O(εN) and L^tot_g ≤ L^tot_b = O(α′).
The same bound holds for every prefix of the QUE rounds."

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
* The sample-level filter is any trajectory of Algorithm 3 with successful approximations
  (`IsStage1Prefix`, `K` completed epochs, rounds `0, …, KT − 1`). "For every prefix of the QUE
  rounds": the totals over rounds `s < t` for every `t ≤ KT`. `L^(s)_g`, `L^(s)_b` are
  `Stage1Traj.lossG`, `Stage1Traj.lossB` with `θ₁ = K₁α′/ε` (zero at rounds without a capped
  update, Definition 5.12).
* "The assumptions of Lemma 5.6 hold whenever a capped update is performed": at every updated round
  `u_i ∈ {0, 1/N}`, `w_{i,j} ≤ 1/n` and `∥vec(p)∥₁ ≥ 1 − C₁ε`, with `C₁` quantified universally
  before `C_Q` and `c`. (Lemma 5.6's condition `σ ≥ C_Qκ` holds automatically at an updated round
  of such a trajectory.) The `O(·)` constant `C` is chosen before `C₁` and `C_Q`: the proof bounds
  `L^tot_b` and `|ℛ̄|` from Definition 5.2, (12) and Lemma 5.10 only, and Lemma 5.14 relies on this.
* "`L^tot_b = O(α′)`" is the upper bound `L^tot_b ≤ Cα′`. `|ℛ̄| = O(εN)` is a property of the data
  and is stated outside the trajectory quantifier. -/
theorem lemma_5_13 :
    ∀ Cref CΔ : ℝ, 0 < Cref → 0 < CΔ →
    ∃ K0min : ℝ, 0 < K0min ∧ ∀ K0 : ℝ, K0min ≤ K0 →
    ∃ K1min : ℝ, ∀ K1 : ℝ, K1min ≤ K1 → 2 * K0 ≤ K1 →
    ∃ C : ℝ, 0 < C ∧ ∀ C1 : ℝ, 0 < C1 →
    ∃ CQmin : ℝ, ∀ CQ : ℝ, CQmin ≤ CQ → ∃ c : ℝ, 0 < c ∧
    ∀ (N n d : ℕ), 1 ≤ N → 1 ≤ n → 1 ≤ d →
    ∀ (ε α δ : ℝ) (z x : Fin N → Fin n → Vec d) (B : Finset (Fin N))
      (I : Finset (Fin N × Fin n)) (μ : Vec d),
      IsContext Cref CΔ ε α δ z x B I μ → ε < c →
      let α' := alphaP Cref N n d α δ
      let κ := kappaP α' (deltaP CΔ α')
      let R := regular K0 α' ε z x B I μ
      10 * K1 * α' < ε →
      ((Finset.univ \ R).card : ℝ) ≤ C * ε * N ∧
      ∀ (tr : Stage1Traj N n) (K : ℕ), IsStage1Prefix x ε α' κ CQ K1 tr K →
        (∀ t < K * epochLen d, tr.Updated d t →
          (∀ i, tr.u t i = 0 ∨ tr.u t i = 1 / (N : ℝ)) ∧ (∀ i j, tr.w t i j ≤ 1 / (n : ℝ)) ∧
            1 - C1 * ε ≤ l1P (prodW (tr.u t) (tr.w t))) →
        ∀ t ≤ K * epochLen d,
          ∑ s ∈ Finset.range t, tr.lossG d (K1 * α' / ε) R (Dset z x I μ) s ≤
              ∑ s ∈ Finset.range t, tr.lossB d (K1 * α' / ε) R (Dset z x I μ) s ∧
            ∑ s ∈ Finset.range t, tr.lossB d (K1 * α' / ε) R (Dset z x I μ) s ≤
              C * α' := by sorry

end DoubleCorrRME
