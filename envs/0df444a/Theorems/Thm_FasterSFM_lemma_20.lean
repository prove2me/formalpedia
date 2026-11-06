-- Prove2me | Theorems.Thm_FasterSFM_lemma_20
-- name    : FasterSFM.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:32.086073+00:00
-- url     : https://prove2.me/theorems/e4e77f5c-49c1-4702-8ab5-c53193e01da3
-- title:
--   Lemma 20 — projection certification and termination of the recentering loop
-- statement:
--   In the setting of Lemma 18 (a phase starting from $x_0$ with $d_\kappa(x_0)\le1/8$), let $x$ be the point returned by RecenterPhase, $u=-\Gamma^\top\Gamma x$ and $\bar x=x+u$. Let $J'$ have orthonormal columns spanning $\ker\Gamma$, $G(y)=J'^\top J^\top\nabla\Psi_{\mathrm{fl}}(Jy)$ and $H'(y)=J'^\top H_S(y)J'$.
--
--   1. If $\|u\|^2_{H_S(x)}\le\tilde\tau^2$, then ProjectAndCheck returns $(\mathrm{true},\bar x)$ at line 6, $\Gamma\bar x=0$, $s_i(J\bar x)>0$ for every row, and
--   $$\|G(\bar x)\|_{H'(\bar x)^{-1}}\ <\ \tau,$$
--   so $\bar x$ is a certified center of the contracted section.
--   2. If $\kappa\ge\kappa^*$, the number of inserted rows is at most $k_n$ and $\Delta\Phi\le B^*$, then $\|u\|^2_{H_S(x)}\le\tilde\tau^2$.
--
--   The first part certifies the output of Recenter; the second bounds the range of the penalty parameter.
--
--   Differences from the source:
--   - reading: "consider a phase" of the algorithm → the phase starts at a point x₀ of the domain with d_κ(x₀) ≤ 1/8; reason: reading R7: Lemmas 17–18 guarantee this at the start of every phase (p.35); stated as a hypothesis
--   - encoding: z_κ, the unique minimizer of Ψ_κ → any z with all slacks of Jz positive minimizing Ψ_κ over that domain; reason: the minimizer is unique, so this is the paper's z_κ
--   - encoding: the body P: cube rows (±e_j, 1) and inserted rows with ‖v_i‖₂ ≤ 1, ρ_i ≥ δ → Body n with the 2n cube rows built in and k inserted rows, Admissible = ‖v_i‖₂ ≤ 1 ∧ δ ≤ ρ_i; reason: Lean encoding of (9); same instances
--   - encoding: min over the section P ∩ S of Ψ_fl → Φ(S, P) = infimum of Ψ_fl over the points of S with all slacks positive; reason: Ψ_fl is +∞ on the boundary in the paper, while Lean's log 0 = 0 would be a junk value; Lemma 9 says the infimum is attained
--   - reading: the termination clause's use of M ≤ M* (Lemma 13) and ∆Φ ≤ B* ((15)) → explicit hypotheses k ≤ k_n and Φ(S′, P) − Φ(S, P) ≤ B*; reason: reading R7
--   - encoding: J′ with orthonormal columns spanning ker Γ (Algorithm 1 line 1) → J′ with J′ᵀJ′ = I and column space = ker Γ; reason: same instances
--   - generalization: J the block basis (ξ_C)_C of S and Γ the r×N matrix with orthonormal rows spanning the coordinates removed by the contraction (§7, p.29) → any J with JᵀJ = I and any Γ with ΓΓᵀ = I; reason: the proof uses only these orthonormality relations; the algorithm's J and Γ are an instance (reading R8)
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 20, p.36 (τ̃, κ*, G, H′ on p.35; Algorithm 3, p.30)

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier
import Definitions.Def_FasterSFM_Recenter

namespace FasterSFM

open Classical Matrix

/-- **Lemma 20** (Projection certification and termination), p.36.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 20, p.36 (`τ̃`, `κ*`, `G`, `H′` on p.35; Algorithm 3, p.30).

"Consider a phase with parameter κ. Let x be the vector returned by RecenterPhase, u = −ΓᵀΓx, and
x̄ = x + u. If ‖u‖²_{H_S(x)} ≤ τ̃², ProjectAndCheck returns (true, x̄) at line 6 and x̄ satisfies
Γx̄ = 0, s_i(Jx̄) > 0 for every inserted or cube row i, and ‖G(x̄)‖_{H′(x̄)⁻¹} < τ. Furthermore, if
κ ≥ κ* then ‖u‖²_{H_S(x)} ≤ τ̃²."

Here `G(y) = J′ᵀJᵀ∇Ψ_fl(Jy)`, `H′(y) = J′ᵀH_S(y)J′`, with `J′` having orthonormal columns spanning
`ker Γ` (Algorithm 1, line 1), and `κ* = max{κ₀, log(8M*W*²(B* + ε)/(λ²δ²τ̃²))}` (p.35).

**Formalization Note.**
* Setting as in Lemma 18; reading R7 for "a phase": `d_κ(x₀) ≤ 1/8` at its start.
* The tolerance in the conclusion is the unbarred `τ` of (12) (the proof ends `< (65/288)τ < τ`).
* Reading R7: the termination clause uses `M ≤ M*` (Lemma 13) and `∆Φ ≤ B*` ((15), p.26), stated as
  the hypotheses `k ≤ k_n` and `Φ(S′, P) − Φ(S, P) ≤ B*`. -/
theorem lemma_20 {n N r N' : ℕ} (P : Body n) (hP : P.Admissible) (J : Matrix (Fin n) (Fin N) ℝ)
    (hJ : Jᵀ * J = 1) (Γ : Matrix (Fin r) (Fin N) ℝ) (hΓ : Γ * Γᵀ = 1)
    (J' : Matrix (Fin N) (Fin N') ℝ) (hJ' : J'ᵀ * J' = 1)
    (hJ'Γ : colSpace J' = LinearMap.ker (Matrix.toLin' Γ)) (κ : ℝ)
    (zκ : Fin N → ℝ) (hz : P.IsPenaltyMin J Γ κ zκ) (x₀ : Fin N → ℝ)
    (hx₀ : P.Interior (J *ᵥ x₀)) (hd : P.dk J Γ κ x₀ ≤ 1 / 8) :
    let x := P.phaseOut J Γ κ x₀
    let u := -((Γᵀ * Γ) *ᵥ x)
    let xb := x + u
    (u ⬝ᵥ (P.HS J x *ᵥ u) ≤ tautilde ^ 2 →
      P.projectAndCheck J Γ x = (true, xb) ∧ Γ *ᵥ xb = 0 ∧ P.Interior (J *ᵥ xb) ∧
      Real.sqrt (invNormSq (P.Hnew J J' xb) (P.Gnew J J' xb)) < tau) ∧
    (kappaStar n ≤ κ → (P.k : ℝ) ≤ kn n →
      P.Phi (contractedSpace J Γ) - P.Phi (colSpace J) ≤ Bstar n →
      u ⬝ᵥ (P.HS J x *ᵥ u) ≤ tautilde ^ 2) := by sorry

end FasterSFM
