-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_5_16
-- name    : DoubleCorrRME.lemma_5_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:27.536772+00:00
-- url     : https://prove2.me/theorems/3f822ca9-8575-4de2-a7fb-3d54c5079c3a
-- title:
--   Lemma 5.16, p.43 — sample-to-user perturbation: $O(\sqrt{\alpha'})$ mean and $O(\alpha'/\varepsilon)$ second moment of $y_i-z^{\rm tr}_i$
-- statement:
--   In the context of Lemma 5.6, let $w$ be the final sample weights of the sample-level filter (Algorithm 3 with successful approximations) and $\mathcal A$ its final active users. For $i\in\mathcal A$ let $s_i=\sum_jw_{i,j}$ and $y_i=\frac1{s_i}\sum_jw_{i,j}x_{i,j}$. Let $\mathcal H\subseteq\mathcal R\cap\mathcal A$ with $|\mathcal H|\ge c_HN$. Then
--
--   $$\Big\|\frac1{|\mathcal H|}\sum_{i\in\mathcal H}(y_i-z^{\mathrm{tr}}_i)\Big\|_2\le C\sqrt{\alpha'},\qquad \frac1{|\mathcal H|}\sum_{i\in\mathcal H}(y_i-z^{\mathrm{tr}}_i)(y_i-z^{\mathrm{tr}}_i)^\top\preceq C\frac{\alpha'}\varepsilon I_d,$$
--
--   with $C$ depending only on $c_H$ and the universal constants.
--
--   The weighted batch means therefore inherit the stability of the truncated batch means up to these perturbations.
--
--   **Formalization Note** Under §4.1, $\kappa=1+C_\Delta^2$ is a constant, so the printed bounds agree with the proof's $O(\sqrt{\alpha'\kappa})$, $O(\alpha'\kappa/\varepsilon)$.
--
--   Differences from the source:
--   - generalization: the universal constants C_ref, C_∆ of §4.1 (and K₀, K₁, C_Q) fixed once → ∀ C_ref, C_∆ > 0, then ∃ thresholds for K₀, K₁, C_Q; later constants may depend on earlier ones; reason: the statement holds for every choice of the §4.1 constants, so it specializes to the paper's fixed choice; every constant is still independent of N, n, d, ε, α, δ and the data
--   - reading: ∆ := O(√α′) (§4.1) and ∆ ← C_∆(√(d/m) + √α′ + √(L/m)) (Algorithm 2, line 2) → ∆ = C_∆√α′, κ = 1 + ∆²/α′; reason: §4.1 is the notation of §§4–5; since d/m, L/m ≤ α′/C_ref the two forms agree up to a change of C_∆, which is universally quantified
--   - reading: the lemma lives on the event of Lemma 4.1 for the corrupted data of Definition 1.1, under Remark 5.4's "we assume ε > 10K₁α′ throughout" and §4.1's δ ∈ (0, 0.1) → explicit hypotheses IsContext (|B| ≤ εN, at most αNn changed points outside B, |ℐ| ≥ (1 − α′)Nn, (α′, ∆)-stability of {z_k : k ∈ ℐ} w.r.t. (µ, I_d), δ ∈ (0, 1/10)) and 10K₁α′ < ε; reason: these are the standing assumptions of §5.2; the lemma is deterministic given them
--   - encoding: N users, n samples per user in ℝ^d → 1 ≤ N, 1 ≤ n, 1 ≤ d; reason: excludes only the empty settings, where the averages divide by 0
--   - reading: the sample-level filter (Algorithm 3) "conditioned on successful power-method and QUE-score approximations" → any trajectory satisfying IsStage1Prefix / IsStage1Run: ν = 1/40, Λ̂_k a ν-approximation of ∥M_s(u^(kT), w^(kT))∥₂, each τ̃^(t) a ν-approximate QUE score matrix for the epoch's MMW density, capped updates at their stopping time; reason: the randomized subroutines are replaced by their success guarantees, exactly as the lemma conditions on them
--   - encoding: |ℋ| = Ω(N) → ∀ c_H > 0, ∃ C, c (depending on c_H), |ℋ| ≥ c_H N; reason: meaning of Ω(N)
--   - encoding: "the final sample weights" w and 𝒜 := 𝒜^(t*) → w = w^(KT), 𝒜 = {i : u^(KT)_i > 0} of a complete run (IsStage1Run); reason: t* is the round at which the filter stops
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 5.16, p.43 (PDF p.44)

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Stability
import Definitions.Def_DoubleCorrRME_Params
import Definitions.Def_DoubleCorrRME_Weights
import Definitions.Def_DoubleCorrRME_Filter

namespace DoubleCorrRME

/-- **Lemma 5.16** (sample-to-user perturbation), p.43 (PDF p.44).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Lemma 5.16 (Sample-to-user perturbation). Let w denote the final sample weights and 𝒜 := 𝒜^(t∗).
For every i ∈ 𝒜, define s_i := ∑_{j=1}^n w_{i,j}, y_i := (1/s_i)∑_{j=1}^n w_{i,j}x_{i,j}, and
M_i(w) := (1/s_i)∑_{j=1}^n w_{i,j}(x_{i,j} − y_i)(x_{i,j} − y_i)ᵀ. Let ℋ ⊆ ℛ ∩ 𝒜 satisfy |ℋ| = Ω(N).
Then:
• Part 1. ∥(1/|ℋ|)∑_{i∈ℋ}(y_i − z^tr_i)∥₂ ≤ O(√α′).
• Part 2. (1/|ℋ|)∑_{i∈ℋ}(y_i − z^tr_i)(y_i − z^tr_i)ᵀ ⪯ O(α′/ε) I_d."

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
* "Final" is the output round `t* = KT` of a complete run of Algorithm 3 with successful
  approximations (`IsStage1Run`); `w = w^(t*)`, `𝒜 = {i : u^(t*)_i > 0}`, `y_i = userMean x w i`,
  `z^tr_i = ztrBatch z ℐ µ i`.
* "`|ℋ| = Ω(N)`": for every `c_H > 0` the constants may depend on `c_H`, and `|ℋ| ≥ c_H N`.
* Under §4.1, `∆ = C_∆√α′`, so `κ = 1 + ∆²/α′ = 1 + C_∆²` is a constant and the printed `O(√α′)`,
  `O(α′/ε)` agree with the proof's `O(√(α′κ))`, `O(α′κ/ε)`.
* `A ⪯ B` is `(B − A).PosSemidef`. -/
theorem lemma_5_16 :
    ∀ Cref CΔ : ℝ, 0 < Cref → 0 < CΔ →
    ∃ K0min : ℝ, 0 < K0min ∧ ∀ K0 : ℝ, K0min ≤ K0 →
    ∃ K1min : ℝ, ∀ K1 : ℝ, K1min ≤ K1 → 2 * K0 ≤ K1 →
    ∃ CQmin : ℝ, ∀ CQ : ℝ, CQmin ≤ CQ → ∀ cH : ℝ, 0 < cH →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (N n d : ℕ), 1 ≤ N → 1 ≤ n → 1 ≤ d →
    ∀ (ε α δ : ℝ) (z x : Fin N → Fin n → Vec d) (B : Finset (Fin N))
      (I : Finset (Fin N × Fin n)) (μ : Vec d),
      IsContext Cref CΔ ε α δ z x B I μ → ε < c →
      let α' := alphaP Cref N n d α δ
      let κ := kappaP α' (deltaP CΔ α')
      10 * K1 * α' < ε →
      ∀ (tr : Stage1Traj N n) (K : ℕ), IsStage1Run x ε α' κ CQ K1 tr K →
        ∀ H : Finset (Fin N),
          H ⊆ regular K0 α' ε z x B I μ ∩ active (tr.u (K * epochLen d)) →
          cH * (N : ℝ) ≤ H.card →
          ‖((H.card : ℝ))⁻¹ • ∑ i ∈ H,
              (userMean x (tr.w (K * epochLen d)) i - ztrBatch z I μ i)‖ ≤ C * Real.sqrt α' ∧
            ((C * α' / ε) • (1 : Matrix (Fin d) (Fin d) ℝ) -
              ((H.card : ℝ))⁻¹ • ∑ i ∈ H,
                outer (userMean x (tr.w (K * epochLen d)) i - ztrBatch z I μ i)).PosSemidef := by sorry

end DoubleCorrRME
