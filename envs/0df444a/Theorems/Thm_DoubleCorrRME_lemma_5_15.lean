-- Prove2me | Theorems.Thm_DoubleCorrRME_lemma_5_15
-- name    : DoubleCorrRME.lemma_5_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:31.539564+00:00
-- url     : https://prove2.me/theorems/8b8bf8f2-4fe0-4e81-b3b0-c52a2d33d5fc
-- title:
--   Lemma 5.15, p.42 — sample covariance reduction: termination, $M_s(u,w)\preceq\frac{16C_Q\kappa}{1-\nu}I_d$, $O(\varepsilon N)$ regular users removed
-- statement:
--   In the context of Lemma 5.6, conditioned on successful power-method and QUE-score approximations, the sample-level filter (Algorithm 3, $\nu=1/40$):
--
--   1. **terminates**: every completed epoch at least halves $\|M_s(u,w)\|_2$, and no run continues forever;
--   2. ends with
--
--   $$M_s(u,w)\preceq\frac{16C_Q\kappa}{1-\nu}I_d ;$$
--
--   3. removes at most $C\varepsilon N$ regular good users.
--
--   This gives the sample-level covariance bound that the user-level stage starts from.
--
--   Differences from the source:
--   - generalization: the universal constants C_ref, C_∆ of §4.1 (and K₀, K₁, C_Q) fixed once → ∀ C_ref, C_∆ > 0, then ∃ thresholds for K₀, K₁, C_Q; later constants may depend on earlier ones; reason: the statement holds for every choice of the §4.1 constants, so it specializes to the paper's fixed choice; every constant is still independent of N, n, d, ε, α, δ and the data
--   - reading: ∆ := O(√α′) (§4.1) and ∆ ← C_∆(√(d/m) + √α′ + √(L/m)) (Algorithm 2, line 2) → ∆ = C_∆√α′, κ = 1 + ∆²/α′; reason: §4.1 is the notation of §§4–5; since d/m, L/m ≤ α′/C_ref the two forms agree up to a change of C_∆, which is universally quantified
--   - reading: the lemma lives on the event of Lemma 4.1 for the corrupted data of Definition 1.1, under Remark 5.4's "we assume ε > 10K₁α′ throughout" and §4.1's δ ∈ (0, 0.1) → explicit hypotheses IsContext (|B| ≤ εN, at most αNn changed points outside B, |ℐ| ≥ (1 − α′)Nn, (α′, ∆)-stability of {z_k : k ∈ ℐ} w.r.t. (µ, I_d), δ ∈ (0, 1/10)) and 10K₁α′ < ε; reason: these are the standing assumptions of §5.2; the lemma is deterministic given them
--   - encoding: N users, n samples per user in ℝ^d → 1 ≤ N, 1 ≤ n, 1 ≤ d; reason: excludes only the empty settings, where the averages divide by 0
--   - reading: the sample-level filter (Algorithm 3) "conditioned on successful power-method and QUE-score approximations" → any trajectory satisfying IsStage1Prefix / IsStage1Run: ν = 1/40, Λ̂_k a ν-approximation of ∥M_s(u^(kT), w^(kT))∥₂, each τ̃^(t) a ν-approximate QUE score matrix for the epoch's MMW density, capped updates at their stopping time; reason: the randomized subroutines are replaced by their success guarantees, exactly as the lemma conditions on them
--   - generalization: "the sample-level filter terminates" → (a) each completed epoch at least halves ∥M_s∥₂ and (b) no trajectory satisfies IsStage1Prefix for every K; reason: (b) is termination of the while loop; (a) is an added clause, stated in the proof ("The covariance halves at each epoch, so the filter terminates", p.43) and implying (b), so the statement contains the printed one
--   - encoding: "only O(εN) regular good users are removed" → |ℛ \ 𝒜^(t*)| ≤ CεN at the end of every complete run; reason: a removed user is one with u_i = 0 at the end
-- source:
--   Aliakbarpour, Liu, Yin, Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time and Sub-Gaussian Rate, STOC 2027 submission (manuscript sha256 49e26e5e…), Lemma 5.15, p.42 (PDF p.43)

import Mathlib
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
import Definitions.Def_DoubleCorrRME_Model
import Definitions.Def_DoubleCorrRME_Stability
import Definitions.Def_DoubleCorrRME_Params
import Definitions.Def_DoubleCorrRME_Weights
import Definitions.Def_DoubleCorrRME_Filter

namespace DoubleCorrRME

/-- **Lemma 5.15** (sample covariance reduction), p.42 (PDF p.43).

Aliakbarpour, Liu, Yin, *Robust Mean Estimation Under Strong Double Corruption: Near-Linear Time
and Sub-Gaussian Rate*, STOC 2027 submission (manuscript sha256 49e26e5e…).

"Lemma 5.15 (Sample covariance reduction). Conditioned on successful power-method and QUE-score
approximations, the sample-level filter terminates with M_s(u, w) ⪯ (16C_Qκ/(1 − ν)) I_d.
Moreover, only O(εN) regular good users are removed."

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
* "Conditioned on successful approximations" is built into `IsStage1Prefix` / `IsStage1Run`
  (`ν = 1/40`). The three clauses:
  1. **termination**, in two forms: every completed epoch at least halves `∥M_s∥₂` (what the proof
     shows), and no trajectory satisfies `IsStage1Prefix` for every `K` (the loop cannot run
     forever);
  2. every complete run ends with `M_s(u, w) ⪯ (16C_Qκ/(1 − ν)) I_d`;
  3. at most `CεN` regular good users are inactive at the end (`|ℛ \ 𝒜^(t*)| ≤ CεN`).
* `A ⪯ B` is `(B − A).PosSemidef`. -/
theorem lemma_5_15 :
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
      (∀ (tr : Stage1Traj N n) (K : ℕ), IsStage1Prefix x ε α' κ CQ K1 tr (K + 1) →
        HighDimProb.QuadraticForms.opNorm
            (covS x (tr.u ((K + 1) * epochLen d)) (tr.w ((K + 1) * epochLen d))) ≤
          HighDimProb.QuadraticForms.opNorm
            (covS x (tr.u (K * epochLen d)) (tr.w (K * epochLen d))) / 2) ∧
      (∀ tr : Stage1Traj N n, ¬ ∀ K : ℕ, IsStage1Prefix x ε α' κ CQ K1 tr K) ∧
      ∀ (tr : Stage1Traj N n) (K : ℕ), IsStage1Run x ε α' κ CQ K1 tr K →
        ((16 * CQ * κ / (1 - nu)) • (1 : Matrix (Fin d) (Fin d) ℝ) -
            covS x (tr.u (K * epochLen d)) (tr.w (K * epochLen d))).PosSemidef ∧
          ((regular K0 α' ε z x B I μ \ active (tr.u (K * epochLen d))).card : ℝ) ≤
            C * ε * N := by sorry

end DoubleCorrRME
