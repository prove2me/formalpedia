-- Prove2me | Theorems.Thm_FasterSFM_lemma_22
-- name    : FasterSFM.lemma_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:45.309837+00:00
-- url     : https://prove2.me/theorems/cf0416c6-720a-4e43-9817-3236f654fff5
-- title:
--   Lemma 22 — penalty energy pays for the warm paths: $O(\log(n+2)+\Delta\Phi)$ phases per contraction
-- statement:
--   Let $n\ge1$. For one contraction (an admissible body with at most $k_n$ inserted rows, an orthonormal basis $J$ of $S$, $\Gamma$ with orthonormal rows, a certified center $x_{\mathrm{in}}$ of $P\cap S$, and $\Delta\Phi=\Phi(S',P)-\Phi(S,P)\le B^*$), Recenter$(x_{\mathrm{in}})$ terminates after at most
--
--   $$1+\frac{16\,\Delta\Phi}{\vartheta_0}+\frac2{\vartheta_0}\,(\vartheta_0+\kappa^*-\kappa_0)\ =\ O(\log(n+2)+\Delta\Phi)$$
--
--   phases (calls of RecenterPhase), with at most four Newton steps per phase; here $\kappa^*-\kappa_0\le C\log(n+2)$ for an absolute $C$. Over all contractions — at most $n-1$ of them, with $\sum_j\Delta\Phi_j\le B^*$ — the total number of phases is at most $Cn\log(n+2)$ and the total number of Newton steps at most $4Cn\log(n+2)$, for an absolute constant $C$.
--
--   This is the bound that makes recentering after contractions cheap: its total cost is paid by the bounded potential.
--
--   Differences from the source:
--   - reading: the per-contraction and total bounds use M ≤ M* (Lemma 13) and the budget Σ_j ∆Φ_j ≤ B* ((15)) with at most n − 1 contractions → explicit hypotheses k ≤ k_n, ∆Φ ≤ B* per contraction, and Σ_j ∆Φ_j ≤ B* over a family of at most n − 1 contraction events; reason: reading R7
--   - reading: O(·) bounds → explicit absolute constants C chosen before n; n ≥ 1; reason: reading R1
--   - generalization: O(log(n + 2) + ∆Φ) phases per contraction → the explicit bound 1 + 16∆Φ/ϑ₀ + (2/ϑ₀)(ϑ₀ + κ* − κ₀) of the proof (p.40) together with κ* − κ₀ ≤ C log(n+2); reason: the explicit bound implies the O-bound
--   - encoding: Recenter (Algorithm 1) and its phases → recenterRun, the iteration of the loop body; phases and Newton steps counted in the state; reason: Lean model of the pseudocode
--   - encoding: the body P: cube rows (±e_j, 1) and inserted rows with ‖v_i‖₂ ≤ 1, ρ_i ≥ δ → Body n with the 2n cube rows built in and k inserted rows, Admissible = ‖v_i‖₂ ≤ 1 ∧ δ ≤ ρ_i; reason: Lean encoding of (9); same instances
--   - encoding: min over the section P ∩ S of Ψ_fl → Φ(S, P) = infimum of Ψ_fl over the points of S with all slacks positive; reason: Ψ_fl is +∞ on the boundary in the paper, while Lean's log 0 = 0 would be a junk value; Lemma 9 says the infimum is attained
--   - generalization: J the block basis (ξ_C)_C of S and Γ the r×N matrix with orthonormal rows spanning the coordinates removed by the contraction (§7, p.29) → any J with JᵀJ = I and any Γ with ΓΓᵀ = I; reason: the proof uses only these orthonormality relations; the algorithm's J and Γ are an instance (reading R8)
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 22, p.39; explicit bound p.40

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier
import Definitions.Def_FasterSFM_Recenter

namespace FasterSFM

open Classical Matrix

/-- **Lemma 22** (Penalty energy pays for the warm paths), p.39.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 22, p.39, with the explicit bound at the end of its proof,
p.40.

"Recenter executes O(log(n + 2) + ∆Φ) phases for one contraction and O(n log(n + 2)) phases over all
contractions. The total number of Newton steps has the same respective bounds. Here a phase is one call
to RecenterPhase at line 5."

Explicit bound (p.40): `1 + 16∆Φ/ϑ₀ + (2/ϑ₀)(ϑ₀ + κ* − κ₀) = O(∆Φ + log(n + 2))` phases, with
`κ* − κ₀ = O(log(n + 2))` (p.35).

**Formalization Note.**
* Recenter is `recenterRun` (Algorithm 1 from `κ₀ = log(τ/(8n))`); the state records the number of
  executed phases and of Newton steps. "Executes at most `B` phases" is: some pass of the outer loop
  reaches the `break` (termination), and the phase count there is at most `B`.
* One contraction: an admissible body, `S` the column space of `J` (`JᵀJ = I`), `Γ` with orthonormal
  rows, `S′ = J ker Γ`, and `x_in` a certified center of `P ∩ S` (12). Reading R7: `M ≤ M*`
  (`k ≤ k_n`, Lemma 13) and `∆Φ ≤ B*` ((15)) are explicit hypotheses.
* `O(·)` is an explicit absolute constant chosen before `n` (reading R1); `n ≥ 1` (R1).
* All contractions: any family of at most `n − 1` contraction events (each satisfying the hypotheses
  above) whose potential increases sum to at most `B*` ((15), reading R7). -/
theorem lemma_22 :
    (∀ {n N r : ℕ} (P : Body n), P.Admissible →
      ∀ (J : Matrix (Fin n) (Fin N) ℝ), Jᵀ * J = 1 →
      ∀ (Γ : Matrix (Fin r) (Fin N) ℝ), Γ * Γᵀ = 1 →
      ∀ (xin : Fin N → ℝ), P.Certified J xin → (P.k : ℝ) ≤ kn n →
      P.Phi (contractedSpace J Γ) - P.Phi (colSpace J) ≤ Bstar n →
      ∃ j : ℕ, (P.recenterRun J Γ xin j).2.2.1 = true ∧
        ((P.recenterRun J Γ xin j).2.2.2.1 : ℝ) ≤
          1 + 16 * (P.Phi (contractedSpace J Γ) - P.Phi (colSpace J)) / theta0 +
            2 / theta0 * (theta0 + kappaStar n - kappa0 n) ∧
        (P.recenterRun J Γ xin j).2.2.2.2 ≤ 4 * (P.recenterRun J Γ xin j).2.2.2.1) ∧
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → kappaStar n - kappa0 n ≤ C * Real.log ((n : ℝ) + 2)) ∧
    (∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ), m ≤ n - 1 →
      ∀ (Nj rj : Fin m → ℕ) (Pj : Fin m → Body n)
        (Jj : ∀ j, Matrix (Fin n) (Fin (Nj j)) ℝ) (Γj : ∀ j, Matrix (Fin (rj j)) (Fin (Nj j)) ℝ)
        (xj : ∀ j, Fin (Nj j) → ℝ),
      (∀ j, (Pj j).Admissible ∧ (Jj j)ᵀ * Jj j = 1 ∧ Γj j * (Γj j)ᵀ = 1 ∧
        (Pj j).Certified (Jj j) (xj j) ∧ ((Pj j).k : ℝ) ≤ kn n) →
      ∑ j, ((Pj j).Phi (contractedSpace (Jj j) (Γj j)) - (Pj j).Phi (colSpace (Jj j))) ≤ Bstar n →
      ∃ steps : Fin m → ℕ,
        (∀ j, ((Pj j).recenterRun (Jj j) (Γj j) (xj j) (steps j)).2.2.1 = true) ∧
        (∑ j, (((Pj j).recenterRun (Jj j) (Γj j) (xj j) (steps j)).2.2.2.1 : ℝ)) ≤
          C * n * Real.log ((n : ℝ) + 2) ∧
        (∑ j, (((Pj j).recenterRun (Jj j) (Γj j) (xj j) (steps j)).2.2.2.2 : ℝ)) ≤
          4 * (C * n * Real.log ((n : ℝ) + 2))) := by sorry

end FasterSFM
