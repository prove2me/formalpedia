-- Prove2me | Theorems.Thm_ExpConeIPM_Corrector_lemma_2
-- name    : ExpConeIPM.Corrector.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:19.556805+00:00
-- url     : https://prove2.me/theorems/ab40d3dc-9568-4379-837b-537a51577e1a
-- title:
--   Lemma 2 — the affine direction (11) is orthogonal and scales the complementarity gap by $1-\alpha$
-- statement:
--   Work in the homogeneous model: $A\colon\mathbb R^n\to\mathbb R^m$ has full row rank, $\hat K$ is a proper cone with a $\hat\vartheta$-logarithmically homogeneous self-concordant barrier $\hat F$, $K=\hat K\times\mathbb R_+$, $F(\hat x,\tau)=\hat F(\hat x)-\log\tau$, and $G$ is the residual of the homogeneous self-dual embedding. Let $z=(x,s,y)$ be an iterate with $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$, and let $W$ be a nonsingular scaling satisfying the double secant equations (8), $v=Wx=W^{-T}s$, $\tilde v=W\tilde x=W^{-T}\tilde s$.
--
--   Then every solution $\Delta z^{a}=(\Delta x^{a},\Delta s^{a},\Delta y^{a})$ of the affine system (11),
--   $$G(\Delta z^{a})=-G(z),\qquad W\Delta x^{a}+W^{-T}\Delta s^{a}=-v,$$
--   satisfies
--   $$\langle s,\Delta x^{a}\rangle+\langle x,\Delta s^{a}\rangle=-\langle x,s\rangle,\qquad \langle\Delta x^{a},\Delta s^{a}\rangle=0, \tag{12}$$
--   and for all $\alpha\in\mathbb R$,
--   $$\langle x+\alpha\Delta x^{a},s+\alpha\Delta s^{a}\rangle=(1-\alpha)\langle x,s\rangle .$$
--
--   A full affine step therefore annihilates both the residual and the complementarity gap. The orthogonality $\langle\Delta x^{a},\Delta s^{a}\rangle=0$ is also what makes the corrector of Lemma 3 neutral for the gap.
--
--   **Formalization Note** The inner products are on $\mathbb R^{n+1}$ and include the homogenizing coordinates: $\langle x,s\rangle=\langle\hat x,\hat s\rangle+\tau\kappa$. Full row rank of $A$ is the paper's standing assumption, stated as surjectivity of $A$. A single proper cone $\hat K$ stands for the paper's product of cones, and $W$ is any nonsingular linear map satisfying (8), not necessarily block diagonal; both are generalizations of the paper's setting.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 351, Lemma 2

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_ExpConeIPM_Corrector_HomogeneousModel
import Definitions.Def_ExpConeIPM_Corrector_SearchDirections

open scoped InnerProductSpace

namespace ExpConeIPM.Corrector

/-- **Lemma 2** (Dahl–Andersen, Math. Program. 194 (2022), p. 351). Standing setting (§2–§4): `A`
has full row rank, `K̂` is a proper cone with a `ϑ̂`-LHSCB `F̂`, the homogeneous model uses
`K = K̂ × ℝ₊`, `F = F̂ − log τ`; `z = (x, s, y) ∈ int(D)`; `W` is a nonsingular scaling satisfying the
double secant equations (8). Every solution `Δzᵃ` of the affine system (11) satisfies (12):
`⟨s, Δxᵃ⟩ + ⟨x, Δsᵃ⟩ = −⟨x, s⟩`, `⟨Δxᵃ, Δsᵃ⟩ = 0`, and
`⟨x + αΔxᵃ, s + αΔsᵃ⟩ = (1 − α)⟨x, s⟩` for all `α ∈ ℝ`. -/
theorem lemma_2 {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n))
    (hA : Function.Surjective A)
    (Khat : Set (EuclideanSpace ℝ (Fin n))) (Fhat : EuclideanSpace ℝ (Fin n) → ℝ) (ϑhat : ℝ)
    (hK : SelfScaledIPM.ShortStep.IsProperCone Khat)
    (hF : SelfScaledIPM.ShortStep.IsLogHomBarrier Khat Fhat ϑhat)
    (x s : EuclideanSpace ℝ (Fin (n + 1))) (y : EuclideanSpace ℝ (Fin m))
    (hz : IsInteriorIterate Khat x s)
    (W : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hW : IsDoubleSecantScaling (augCone Khat) (augBarrier Fhat) x s W)
    (dxa dsa : EuclideanSpace ℝ (Fin (n + 1))) (dya : EuclideanSpace ℝ (Fin m))
    (ha : IsAffineDirection A b c x s y W dxa dsa dya) :
    ⟪s, dxa⟫_ℝ + ⟪x, dsa⟫_ℝ = -⟪x, s⟫_ℝ ∧ ⟪dxa, dsa⟫_ℝ = 0 ∧
      ∀ α : ℝ, ⟪x + α • dxa, s + α • dsa⟫_ℝ = (1 - α) * ⟪x, s⟫_ℝ := by sorry

end ExpConeIPM.Corrector
