-- Prove2me | Theorems.Thm_FasterSFM_lemma_18
-- name    : FasterSFM.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:45.353198+00:00
-- url     : https://prove2.me/theorems/099c9905-8e7f-4773-ab00-dbc13f9371d6
-- title:
--   Lemma 18 — Newton steps during a phase: at most 4 steps, decrement, slack and penalty guarantees
-- statement:
--   Let $P$ be an admissible body, $J$ an orthonormal basis of $S$, $\Gamma$ a matrix with orthonormal rows, $S'=J\ker\Gamma$, and $z_\kappa$ the minimizer of $\Psi_\kappa$ over $\{x:s_i(Jx)>0\}$. Let $x_0$ be a point of that domain with $d_\kappa(x_0)\le1/8$. Then RecenterPhase$(\kappa,x_0)$ stops after at most 4 Newton iterations, and the returned point $x$ satisfies:
--
--   1. **decrement guarantee:** with $\mu=e^{\kappa/2}\|\Gamma x\|_2$, $\vartheta=\vartheta_0/\max\{1,\mu\}$ and $\kappa_+=\kappa+\log(1+\vartheta)$, one has $d_{\kappa_+}(x)\le1/8$;
--   2. **slack guarantee:** for every inserted or cube row, $\tfrac12s_i(Jz_\kappa)\le s_i(Jx)\le\tfrac32s_i(Jz_\kappa)$;
--   3. **penalty guarantee:** with $\Delta\Phi=\Phi(S',P)-\Phi(S,P)$ and $\varepsilon=\bar\tau^2/\lambda$,
--   $$\frac{e^\kappa}{2}\|\Gamma x\|_2^2\ \le\ \Delta\Phi+\varepsilon .$$
--
--   Each phase of the recentering path therefore costs a constant number of Newton steps and hands a good starting point to the next phase.
--
--   Differences from the source:
--   - encoding: z_κ, the unique minimizer of Ψ_κ → any z with all slacks of Jz positive minimizing Ψ_κ over that domain; reason: the minimizer is unique, so this is the paper's z_κ
--   - encoding: the body P: cube rows (±e_j, 1) and inserted rows with ‖v_i‖₂ ≤ 1, ρ_i ≥ δ → Body n with the 2n cube rows built in and k inserted rows, Admissible = ‖v_i‖₂ ≤ 1 ∧ δ ≤ ρ_i; reason: Lean encoding of (9); same instances
--   - encoding: min over the section P ∩ S of Ψ_fl → Φ(S, P) = infimum of Ψ_fl over the points of S with all slacks positive; reason: Ψ_fl is +∞ on the boundary in the paper, while Lean's log 0 = 0 would be a junk value; Lemma 9 says the infimum is attained
--   - encoding: κ₊ = κ + log(1 + ϑ), "the parameter of the next phase" → ϑ = ϑ₀/max{1, e^{κ/2}‖Γx‖₂}, the value set at Algorithm 1 line 10; reason: the next phase's parameter as the algorithm defines it
--   - encoding: "terminates in at most 4 iterations" → some Newton iterate with index ≤ 4 passes the test of Algorithm 2 line 3, and the number of executed steps is ≤ 4; reason: the loop modelled as its sequence of iterates
--   - encoding: x₀ the initial point of the phase → x₀ with all slacks of Jx₀ positive; reason: the phase runs in the domain of Ψ_κ
--   - generalization: J the block basis (ξ_C)_C of S and Γ the r×N matrix with orthonormal rows spanning the coordinates removed by the contraction (§7, p.29) → any J with JᵀJ = I and any Γ with ΓΓᵀ = I; reason: the proof uses only these orthonormality relations; the algorithm's J and Γ are an instance (reading R8)
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 18, p.32 (Algorithms 1–2, p.30)

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier
import Definitions.Def_FasterSFM_Recenter

namespace FasterSFM

open Classical Matrix

/-- **Lemma 18** (Newton steps during a phase), p.32.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 18, p.32 (Algorithms 1–2, p.30).

"Consider a phase with parameter κ, and let z_κ be the unique minimizer of Ψ_κ and thus f_κ. Let x₀
be the initial point at the start of the phase. If d_κ(x₀) ≤ 1/8, RecenterPhase(κ, x₀) terminates in
at most 4 iterations of Newton's method and it returns a vector x with the following properties:
1. Decrement guarantee: Let κ₊ = κ + log(1 + ϑ) be the parameter of the next phase. We have
   d_{κ₊}(x) ≤ 1/8.
2. Slack guarantee: For every inserted or cube row, ½ s_i(Jz_κ) ≤ s_i(Jx) ≤ (3/2) s_i(Jz_κ).
3. Penalty guarantee: Let ∆Φ := Φ(S′, P) − Φ(S, P) and ε := τ̄²/λ. We have
   (e^κ/2)‖Γx‖₂² ≤ ∆Φ + ε."

**Formalization Note.**
* `S` is the column space of `J` (`JᵀJ = I`), `Γ` has orthonormal rows (`ΓΓᵀ = I_r`) and
  `S′ = J ker Γ`; the body is admissible (cube rows plus rows with `‖v_i‖₂ ≤ 1`, `ρ_i ≥ δ`).
* `z_κ` is a minimizer of `Ψ_κ` over the domain `{x : s_i(Jx) > 0}` (unique by the lemma's own
  premise); `x₀` lies in the domain.
* "Terminates in at most 4 iterations": some iterate with index `≤ 4` passes the test of Algorithm 2,
  line 3 (so the loop stops after at most 4 Newton steps); `x` is the first passing iterate.
* `ϑ` is the value set at Algorithm 1, line 10: `ϑ = ϑ₀/max{1, µ}` with `µ = e^{κ/2}‖Γx‖₂`.
* The text layer prints `τ̄` as `τ`; on the page `ε = τ̄²/λ` with `τ̄ = τ/8`. -/
theorem lemma_18 {n N r : ℕ} (P : Body n) (hP : P.Admissible) (J : Matrix (Fin n) (Fin N) ℝ)
    (hJ : Jᵀ * J = 1) (Γ : Matrix (Fin r) (Fin N) ℝ) (hΓ : Γ * Γᵀ = 1) (κ : ℝ)
    (zκ : Fin N → ℝ) (hz : P.IsPenaltyMin J Γ κ zκ) (x₀ : Fin N → ℝ)
    (hx₀ : P.Interior (J *ᵥ x₀)) (hd : P.dk J Γ κ x₀ ≤ 1 / 8) :
    let x := P.phaseOut J Γ κ x₀
    (∃ k ≤ 4, P.phaseTest J Γ κ (P.phaseIter J Γ κ x₀ k)) ∧
    P.phaseSteps J Γ κ x₀ ≤ 4 ∧
    P.dk J Γ (κ + Real.log (1 + theta0 / max 1 (Real.exp (κ / 2) * Real.sqrt (sqNorm (Γ *ᵥ x)))))
      x ≤ 1 / 8 ∧
    (∀ i, P.slack i (J *ᵥ zκ) / 2 ≤ P.slack i (J *ᵥ x) ∧
      P.slack i (J *ᵥ x) ≤ 3 / 2 * P.slack i (J *ᵥ zκ)) ∧
    Real.exp κ / 2 * sqNorm (Γ *ᵥ x) ≤
      (P.Phi (contractedSpace J Γ) - P.Phi (colSpace J)) + eps := by sorry

end FasterSFM
