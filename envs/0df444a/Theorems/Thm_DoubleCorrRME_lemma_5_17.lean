-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_5_17
-- name    : DoubleCorrRME.lemma_5_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:36.532507+00:00
-- url     : https://prove2.me/theorems/766c1811-d8bb-48bc-8ae1-cb4618fafc84
-- title:
--   Lemma 5.17, p.46 — good user representatives: $|\mathcal H|\ge(1-C_H\varepsilon)N$, mean $O(\Delta+\rho+\sqrt{\alpha'\kappa})$, $\|\Sigma\|_2\le O(\Lambda)$
-- statement:
--   In the context of Lemma 5.6, let the second stable reference of Lemma 4.1 hold: $\mathcal J\subseteq[N]$ with $|\mathcal J|\ge(1-\varepsilon/4)N$ and $\{z^{\mathrm{tr}}_i:i\in\mathcal J\}$ $(\varepsilon/4,C_S\rho)$-stable with respect to $(\bar z^{\mathrm{tr}},\lambda I_d)$. Let $w,\mathcal A,y_i$ be as in Lemma 5.16 and $\Lambda=\lambda+\alpha'\kappa/\varepsilon$. There is a set $\mathcal H\subseteq\mathcal R\cap\mathcal A$ such that, with $S^y_{\mathcal H}=\{y_i:i\in\mathcal H\}$,
--
--   1. $|\mathcal H|\ge(1-C_H\varepsilon)N$ for a sufficiently large universal constant $C_H$;
--   2. $\|\mu_{S^y_{\mathcal H}}-\mu\|_2\le C(\Delta+\rho+\sqrt{\alpha'\kappa})$;
--   3. $\|\Sigma_{S^y_{\mathcal H}}\|_2\le C\Lambda$.
--
--   These are the bounded-covariance good-core conditions under which the final one-level estimator on the weighted batch means achieves the target rate.
--
--   Differences from the source:
--   - generalization: the universal constants C_ref, C_∆ of §4.1 (and K₀, K₁, C_Q) fixed once → ∀ C_ref, C_∆ > 0, then ∃ thresholds for K₀, K₁, C_Q; later constants may depend on earlier ones; reason: the statement holds for every choice of the §4.1 constants, so it specializes to the paper's fixed choice; every constant is still independent of N, n, d, ε, α, δ and the data
--   - reading: ∆ := O(√α′) (§4.1) and ∆ ← C_∆(√(d/m) + √α′ + √(L/m)) (Algorithm 2, line 2) → ∆ = C_∆√α′, κ = 1 + ∆²/α′; reason: §4.1 is the notation of §§4–5; since d/m, L/m ≤ α′/C_ref the two forms agree up to a change of C_∆, which is universally quantified
--   - reading: the lemma lives on the event of Lemma 4.1 for the corrupted data of Definition 1.1, under Remark 5.4's "we assume ε > 10K₁α′ throughout" and §4.1's δ ∈ (0, 0.1) → explicit hypotheses IsContext (|B| ≤ εN, at most αNn changed points outside B, |ℐ| ≥ (1 − α′)Nn, (α′, ∆)-stability of {z_k : k ∈ ℐ} w.r.t. (µ, I_d), δ ∈ (0, 1/10)) and 10K₁α′ < ε; reason: these are the standing assumptions of §5.2; the lemma is deterministic given them
--   - encoding: N users, n samples per user in ℝ^d → 1 ≤ N, 1 ≤ n, 1 ≤ d; reason: excludes only the empty settings, where the averages divide by 0
--   - reading: the sample-level filter (Algorithm 3) "conditioned on successful power-method and QUE-score approximations" → any trajectory satisfying IsStage1Prefix / IsStage1Run: ν = 1/40, Λ̂_k a ν-approximation of ∥M_s(u^(kT), w^(kT))∥₂, each τ̃^(t) a ν-approximate QUE score matrix for the epoch's MMW density, capped updates at their stopping time; reason: the randomized subroutines are replaced by their success guarantees, exactly as the lemma conditions on them
--   - reading: "Let 𝒥 be the index set of the second stable set S_2 from Lemma 4.1" (proof) → hypothesis: 𝒥 with |𝒥| ≥ (1 − ε/4)N and (ε/4, C_Sρ)-stability w.r.t. (z̄^tr, λI_d), for every C_ρ, C_S > 0; reason: the lemma lives on the event of Lemma 4.1; the constants are universally quantified like those of §4.1
--   - encoding: C_H and O(·) → ∃ C_H, C > 0 after C_Q; reason: meaning of the universal constants
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 5.17, p.46 (PDF p.47)

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Stability
import Definitions.Def_DoubleCorrRME_Params
import Definitions.Def_DoubleCorrRME_Weights
import Definitions.Def_DoubleCorrRME_Filter

namespace DoubleCorrRME

/-- **Lemma 5.17** (good user representatives), p.46 (PDF p.47).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Lemma 5.17 (Good user representatives). Let S^y_ℋ := {y_i : i ∈ ℋ} and Λ := λ + α′κ/ε. There exists a
set ℋ ⊆ ℛ ∩ 𝒜 such that
• Part 1. |ℋ| ≥ (1 − C_Hε)N for a sufficiently large universal constant C_H > 0;
• Part 2. ∥µ_{S^y_ℋ} − µ∥₂ ≤ O(∆ + ρ + √(α′κ));
• Part 3. ∥Σ_{S^y_ℋ}∥₂ ≤ O(Λ)."

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
* The second reference (Lemma 4.1, Part 2) is a hypothesis: `𝒥 ⊆ [N]` with `|𝒥| ≥ (1 − ε/4)N` and
  `{z^tr_i : i ∈ 𝒥}` `(ε/4, C_Sρ)`-stable with respect to `(z̄^tr, λI_d)`, for every choice of the
  constants `C_ρ, C_S > 0` of §4.1 and of Lemma 4.1 (`ρ = rhoP C_ρ κ …`, `λ = ρ²/ε`).
* `y_i`, `𝒜` are those of the final round `t* = KT` of a complete run (`IsStage1Run`), as in
  Lemma 5.16. `µ_S` is the mean and `Σ_S = (1/|S|)∑(x − µ_S)(x − µ_S)ᵀ` the covariance of the multiset
  `{y_i : i ∈ ℋ}` (p.4); `∥·∥₂` is the spectral norm.
* `C_H` and the `O(·)` constant `C` are existential, after `C_Q`. -/
theorem lemma_5_17 :
    ∀ Cref CΔ Cρ CS : ℝ, 0 < Cref → 0 < CΔ → 0 < Cρ → 0 < CS →
    ∃ K0min : ℝ, 0 < K0min ∧ ∀ K0 : ℝ, K0min ≤ K0 →
    ∃ K1min : ℝ, ∀ K1 : ℝ, K1min ≤ K1 → 2 * K0 ≤ K1 →
    ∃ CQmin : ℝ, ∀ CQ : ℝ, CQmin ≤ CQ →
    ∃ CH : ℝ, 0 < CH ∧ ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (N n d : ℕ), 1 ≤ N → 1 ≤ n → 1 ≤ d →
    ∀ (ε α δ : ℝ) (z x : Fin N → Fin n → Vec d) (B : Finset (Fin N))
      (I : Finset (Fin N × Fin n)) (μ : Vec d),
      IsContext Cref CΔ ε α δ z x B I μ → ε < c →
      let α' := alphaP Cref N n d α δ
      let Δ := deltaP CΔ α'
      let κ := kappaP α' Δ
      let ρ := rhoP Cρ κ N n d δ
      let lam := lambdaP ρ ε
      10 * K1 * α' < ε →
      ∀ J : Finset (Fin N), (1 - ε / 4) * (N : ℝ) ≤ J.card →
        IsStable (ztrBatch z I μ) J (ε / 4) (CS * ρ) (ztrMean z I μ) (lam • 1) →
      ∀ (tr : Stage1Traj N n) (K : ℕ), IsStage1Run x ε α' κ CQ K1 tr K →
        ∃ H : Finset (Fin N),
          H ⊆ regular K0 α' ε z x B I μ ∩ active (tr.u (K * epochLen d)) ∧
          (1 - CH * ε) * (N : ℝ) ≤ H.card ∧
          ‖meanOn (userMean x (tr.w (K * epochLen d))) H - μ‖ ≤
            C * (Δ + ρ + Real.sqrt (α' * κ)) ∧
          HighDimProb.QuadraticForms.opNorm (covOn (userMean x (tr.w (K * epochLen d))) H) ≤
            C * (lam + α' * κ / ε) := by sorry

end DoubleCorrRME
