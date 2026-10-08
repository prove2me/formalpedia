-- Prove2me | Theorems.Thm_ExpConeIPM_Corrector_lemma_3
-- name    : ExpConeIPM.Corrector.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:01.677204+00:00
-- url     : https://prove2.me/theorems/13d45bd6-3fa7-44a8-9937-20809c5929cd
-- title:
--   Lemma 3 — the pure corrector direction (17) is orthogonal and leaves the complementarity gap unchanged to first order
-- statement:
--   Work in the setting of Lemma 2: the homogeneous model with $K=\hat K\times\mathbb R_+$ and barrier $F(\hat x,\tau)=\hat F(\hat x)-\log\tau$, an iterate $z=(x,s,y)$ with $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$, a nonsingular scaling $W$ satisfying (8), and a solution $\Delta z^{a}$ of the affine system (11). Let
--   $$\eta:=-\tfrac12F'''(x)[\Delta x^{a},(F''(x))^{-1}\Delta s^{a}] \tag{16}$$
--   be the corrector term. Then every solution $\Delta z^{c}=(\Delta x^{c},\Delta s^{c},\Delta y^{c})$ of the pure corrector system (17),
--   $$G(\Delta z^{c})=0,\qquad W\Delta x^{c}+W^{-T}\Delta s^{c}=-W^{-T}\eta,$$
--   satisfies
--   $$\langle s,\Delta x^{c}\rangle+\langle x,\Delta s^{c}\rangle=0,\qquad\langle\Delta x^{c},\Delta s^{c}\rangle=0 .$$
--
--   The corrector therefore changes neither the residual nor the complementarity gap; adding it to the affine and centering directions in (18) does not disturb the uniform decrease established in Lemma 4.
--
--   **Formalization Note** $F''(x)$ is the published `hess`, $F'''(x)[u,w]$ is `fderiv ℝ (hess F) x u w`, and $(F''(x))^{-1}$ is `ContinuousLinearMap.inverse` (the true inverse: the augmented barrier has a positive definite Hessian at interior points). The barrier in (16) is the augmented $F$, so $\eta$ has a $\tau$-coordinate; inner products include the $\tau\kappa$ terms. Generalizations as in Lemma 2 (one cone $\hat K$, $W$ not assumed block diagonal).
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 352, Lemma 3 (with (16), (17))

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_ExpConeIPM_Corrector_HomogeneousModel
import Definitions.Def_ExpConeIPM_Corrector_SearchDirections

open scoped InnerProductSpace

namespace ExpConeIPM.Corrector

/-- **Lemma 3** (Dahl–Andersen, Math. Program. 194 (2022), p. 352). In the setting of Lemma 2, let
`Δzᵃ` solve the affine system (11), let `η := −½ F'''(x)[Δxᵃ, (F''(x))⁻¹Δsᵃ]` be the corrector (16) of
the augmented barrier `F = F̂ − log τ`, and let `Δzᶜ` solve the pure corrector system (17). Then
`⟨s, Δxᶜ⟩ + ⟨x, Δsᶜ⟩ = 0` and `⟨Δxᶜ, Δsᶜ⟩ = 0`. -/
theorem lemma_3 {n m : ℕ}
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
    (ha : IsAffineDirection A b c x s y W dxa dsa dya)
    (dxc dsc : EuclideanSpace ℝ (Fin (n + 1))) (dyc : EuclideanSpace ℝ (Fin m))
    (hc : IsPureCorrectorDirection A b c W (corrector (augBarrier Fhat) x dxa dsa) dxc dsc dyc) :
    ⟪s, dxc⟫_ℝ + ⟪x, dsc⟫_ℝ = 0 ∧ ⟪dxc, dsc⟫_ℝ = 0 := by sorry

end ExpConeIPM.Corrector
