-- Prove2me | Theorems.Thm_FasterSFM_lemma_19
-- name    : FasterSFM.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:51.548254+00:00
-- url     : https://prove2.me/theorems/552df101-9fbc-454a-992d-f1c449092218
-- title:
--   Lemma 19 — slack lower bounds and a Hessian upper bound along the phases
-- statement:
--   In the setting of Lemma 18 (a phase with parameter $\kappa$ starting from $x_0$ with $d_\kappa(x_0)\le1/8$), let $x$ be the point returned by RecenterPhase and $W=n+\lambda M$. For every inserted or cube row,
--
--   $$s_i(Jz_\kappa)\ \ge\ \frac{\lambda\rho_i}{W},\qquad s_i(Jx)\ \ge\ \frac{\lambda\rho_i}{2W}\ \ge\ \frac{\lambda\delta}{2W},$$
--
--   and
--
--   $$H_S(x)\ \preceq\ \frac{4MW^2}{\lambda^2\delta^2}\,I_N .$$
--
--   These bounds keep the projection step of ProjectAndCheck strictly feasible and convert the penalty bound of Lemma 18 into the projection test of Lemma 20.
--
--   Differences from the source:
--   - reading: "consider a phase" of the algorithm → the phase starts at a point x₀ of the domain with d_κ(x₀) ≤ 1/8; reason: reading R7: Lemmas 17–18 guarantee this at the start of every phase (p.35); stated as a hypothesis
--   - encoding: z_κ, the unique minimizer of Ψ_κ → any z with all slacks of Jz positive minimizing Ψ_κ over that domain; reason: the minimizer is unique, so this is the paper's z_κ
--   - encoding: the body P: cube rows (±e_j, 1) and inserted rows with ‖v_i‖₂ ≤ 1, ρ_i ≥ δ → Body n with the 2n cube rows built in and k inserted rows, Admissible = ‖v_i‖₂ ≤ 1 ∧ δ ≤ ρ_i; reason: Lean encoding of (9); same instances
--   - encoding: H_S(x) ⪯ cI_N → wᵀH_S(x)w ≤ c wᵀw for every w; reason: Loewner order as quadratic forms
--   - generalization: J the block basis (ξ_C)_C of S and Γ the r×N matrix with orthonormal rows spanning the coordinates removed by the contraction (§7, p.29) → any J with JᵀJ = I and any Γ with ΓΓᵀ = I; reason: the proof uses only these orthonormality relations; the algorithm's J and Γ are an instance (reading R8)
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 19, p.34

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier
import Definitions.Def_FasterSFM_Recenter

namespace FasterSFM

open Classical Matrix

/-- **Lemma 19** (Slack lower bounds), p.34.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 19, p.34.

"Consider a phase with parameter κ. Let z_κ be the unique minimizer of Ψ_κ, and let x be the vector
returned by RecenterPhase in that phase. For every inserted or cube row, we have
s_i(Jz_κ) ≥ λρ_i/W and s_i(Jx) ≥ λρ_i/(2W) ≥ λδ/(2W). Additionally, H_S(x) ⪯ (4MW²/(λ²δ²)) I_N."

Here `W = n + λM`.

**Formalization Note.** Setting as in Lemma 18. Reading R7: "a phase" of the algorithm starts at a
point `x₀` of the domain with `d_κ(x₀) ≤ 1/8` (Lemmas 17 and 18, p.35: "Lemmas 17 and 18 guarantee
that the Newton decrement is at most 1/8 at the beginning of each phase"); this is the explicit
hypothesis. `H_S(x) ⪯ cI_N` is stated for the quadratic forms. -/
theorem lemma_19 {n N r : ℕ} (P : Body n) (hP : P.Admissible) (J : Matrix (Fin n) (Fin N) ℝ)
    (hJ : Jᵀ * J = 1) (Γ : Matrix (Fin r) (Fin N) ℝ) (hΓ : Γ * Γᵀ = 1) (κ : ℝ)
    (zκ : Fin N → ℝ) (hz : P.IsPenaltyMin J Γ κ zκ) (x₀ : Fin N → ℝ)
    (hx₀ : P.Interior (J *ᵥ x₀)) (hd : P.dk J Γ κ x₀ ≤ 1 / 8) :
    let x := P.phaseOut J Γ κ x₀
    (∀ i, lam * P.rowρ i / P.W ≤ P.slack i (J *ᵥ zκ)) ∧
    (∀ i, lam * P.rowρ i / (2 * P.W) ≤ P.slack i (J *ᵥ x) ∧
      lam * delta n / (2 * P.W) ≤ lam * P.rowρ i / (2 * P.W)) ∧
    (∀ w : Fin N → ℝ,
      w ⬝ᵥ (P.HS J x *ᵥ w) ≤ 4 * (P.M : ℝ) * P.W ^ 2 / (lam ^ 2 * delta n ^ 2) * (w ⬝ᵥ w)) := by sorry

end FasterSFM
