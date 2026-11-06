-- Prove2me | Theorems.Thm_FasterSFM_lemma_21
-- name    : FasterSFM.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:26.902016+00:00
-- url     : https://prove2.me/theorems/748c82e6-537f-4d7a-98ca-d203c2f0578c
-- title:
--   Lemma 21 — energy along the exact penalty path
-- statement:
--   In the setting of Lemma 18, let $z_\kappa$ be the exact minimizer of $\Psi_\kappa$ for every real $\kappa$, $F(\kappa)=\Psi_\kappa(z_\kappa)$ and $E(\kappa)=e^\kappa\|\Gamma z_\kappa\|_2^2$. Then for every finite $\kappa$
--
--   $$\Phi(S,P)\le F(\kappa)\le\Phi(S',P),\qquad \frac{dF}{d\kappa}=\frac{E(\kappa)}2,\qquad E'(\kappa)\ge-E(\kappa).$$
--
--   In particular $F$ is nondecreasing, and for every $\vartheta\ge0$
--
--   $$F(\kappa+\log(1+\vartheta))-F(\kappa)\ \ge\ \frac{E(\kappa)}2\cdot\frac{\vartheta}{1+\vartheta}. \tag{23}$$
--
--   Finally, if $x$ is the point returned by RecenterPhase from a starting point with $d_\kappa\le1/8$ and $\mu_\kappa=e^{\kappa/2}\|\Gamma x\|_2$, then $|\mu_\kappa-\sqrt{E(\kappa)}|\le\sqrt{2\varepsilon}$.
--
--   The energy $E$ measures how much potential each increase of the penalty consumes; it drives the phase count of Lemma 22.
--
--   Differences from the source:
--   - encoding: z_κ, the exact penalty minimizers, as a function of κ → a function z : ℝ → ℝ^N with z κ a minimizer of Ψ_κ over the domain for every κ; reason: the minimizer is unique, so this is the paper's path
--   - encoding: the body P: cube rows (±e_j, 1) and inserted rows with ‖v_i‖₂ ≤ 1, ρ_i ≥ δ → Body n with the 2n cube rows built in and k inserted rows, Admissible = ‖v_i‖₂ ≤ 1 ∧ δ ≤ ρ_i; reason: Lean encoding of (9); same instances
--   - encoding: min over the section P ∩ S of Ψ_fl → Φ(S, P) = infimum of Ψ_fl over the points of S with all slacks positive; reason: Ψ_fl is +∞ on the boundary in the paper, while Lean's log 0 = 0 would be a junk value; Lemma 9 says the infimum is attained
--   - encoding: dF/dκ = E/2 and E′ ≥ −E → HasDerivAt F (E κ / 2) κ, and E has a derivative E′ at κ with E′ ≥ −E κ; reason: derivatives as in Mathlib
--   - reading: "let x be the point returned by RecenterPhase" → x = RecenterPhase(κ, x₀) for x₀ in the domain with d_κ(x₀) ≤ 1/8; reason: reading R7: the phase's starting condition
--   - generalization: J the block basis (ξ_C)_C of S and Γ the r×N matrix with orthonormal rows spanning the coordinates removed by the contraction (§7, p.29) → any J with JᵀJ = I and any Γ with ΓΓᵀ = I; reason: the proof uses only these orthonormality relations; the algorithm's J and Γ are an instance (reading R8)
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 21, eq. (23), p.37

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier
import Definitions.Def_FasterSFM_Recenter

namespace FasterSFM

open Classical Matrix

/-- **Lemma 21** (Energy along the exact penalty path), p.37.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 21, eq. (23), p.37.

"For finite κ, the functions F and E satisfy Φ(S, P) ≤ F(κ) ≤ Φ(S′, P), dF/dκ = E(κ)/2,
E′(κ) ≥ −E(κ). In particular F is nondecreasing, and for every ϑ ≥ 0 its increase satisfies
F(κ + log(1 + ϑ)) − F(κ) ≥ (E(κ)/2) · ϑ/(1 + ϑ). (23)
Additionally, let x be the point returned by RecenterPhase and µ_κ = e^{κ/2}‖Γx‖₂. We have
|µ_κ − √E(κ)| ≤ √(2ε)."

Here `F(κ) = Ψ_κ(z_κ)`, `E(κ) = e^κ‖Γz_κ‖₂²` (p.37), `z_κ` the exact minimizer of `Ψ_κ`, and
`ε = τ̄²/λ`.

**Formalization Note.**
* Setting as in Lemma 18. `z : ℝ → ℝ^N` is the exact penalty path: `z κ` minimizes `Ψ_κ` over the
  domain for every `κ` (the minimizer is unique, so this is the paper's `z_κ`).
* `dF/dκ = E/2` is `HasDerivAt F (E κ / 2) κ`; `E′ ≥ −E` is: `E` has a derivative `E′(κ)` at `κ`
  and `E′(κ) ≥ −E(κ)`.
* Reading R7 for the last clause: RecenterPhase starts at a point `x₀` of the domain with
  `d_κ(x₀) ≤ 1/8`. -/
theorem lemma_21 {n N r : ℕ} (P : Body n) (hP : P.Admissible) (J : Matrix (Fin n) (Fin N) ℝ)
    (hJ : Jᵀ * J = 1) (Γ : Matrix (Fin r) (Fin N) ℝ) (hΓ : Γ * Γᵀ = 1)
    (z : ℝ → Fin N → ℝ) (hz : ∀ κ, P.IsPenaltyMin J Γ κ (z κ)) :
    let F : ℝ → ℝ := fun κ => P.Psik J Γ κ (z κ)
    let E : ℝ → ℝ := fun κ => Real.exp κ * sqNorm (Γ *ᵥ z κ)
    (∀ κ, P.Phi (colSpace J) ≤ F κ ∧ F κ ≤ P.Phi (contractedSpace J Γ)) ∧
    (∀ κ, HasDerivAt F (E κ / 2) κ) ∧
    (∀ κ, ∃ E' : ℝ, HasDerivAt E E' κ ∧ -E κ ≤ E') ∧
    Monotone F ∧
    (∀ κ ϑ : ℝ, 0 ≤ ϑ → E κ / 2 * (ϑ / (1 + ϑ)) ≤ F (κ + Real.log (1 + ϑ)) - F κ) ∧
    (∀ (κ : ℝ) (x₀ : Fin N → ℝ), P.Interior (J *ᵥ x₀) → P.dk J Γ κ x₀ ≤ 1 / 8 →
      |Real.exp (κ / 2) * Real.sqrt (sqNorm (Γ *ᵥ P.phaseOut J Γ κ x₀)) - Real.sqrt (E κ)| ≤
        Real.sqrt (2 * eps)) := by sorry

end FasterSFM
