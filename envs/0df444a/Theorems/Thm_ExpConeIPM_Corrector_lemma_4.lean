-- Prove2me | Theorems.Thm_ExpConeIPM_Corrector_lemma_4
-- name    : ExpConeIPM.Corrector.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:31.831019+00:00
-- url     : https://prove2.me/theorems/794b81c3-c097-4649-b7e7-b64cb1a8d749
-- title:
--   Lemma 4 — along the combined corrector direction (18) the residuals and the complementarity gap both scale by $1-\alpha(1-\gamma)$
-- statement:
--   Work in the homogeneous model of a conic pair: $A\colon\mathbb R^n\to\mathbb R^m$ has full row rank, $b\in\mathbb R^m$, $c\in\mathbb R^n$, $\hat K\subseteq\mathbb R^n$ is a proper cone with a $\hat\vartheta$-logarithmically homogeneous self-concordant barrier $\hat F$, $K=\hat K\times\mathbb R_+$, $F(\hat x,\tau)=\hat F(\hat x)-\log\tau$, $\vartheta=\hat\vartheta+1$, and $G$ is the residual of the homogeneous self-dual embedding. Let $z=(x,s,y)$ be an iterate with $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$, let $\mu=\langle x,s\rangle/\vartheta$, let $\tilde x=-F_*'(s)$, $\tilde s=-F'(x)$ be the shadow iterates, and let $W$ be a nonsingular scaling with $v=Wx=W^{-T}s$ and $\tilde v=W\tilde x=W^{-T}\tilde s$. Let $\Delta z^{a}$ solve the affine system (11), let $\eta=-\tfrac12F'''(x)[\Delta x^{a},(F''(x))^{-1}\Delta s^{a}]$ be the corrector (16), and let $\gamma>0$ be a centering parameter.
--
--   Then every solution $\Delta z=(\Delta x,\Delta s,\Delta y)$ of the combined system (18),
--   $$G(\Delta z)=-(1-\gamma)G(z),\qquad W\Delta x+W^{-T}\Delta s=-v+\gamma\mu\tilde v-W^{-T}\eta,$$
--   satisfies
--   $$\langle s,\Delta x\rangle+\langle x,\Delta s\rangle=-(1-\gamma)\langle x,s\rangle,\qquad\langle\Delta x,\Delta s\rangle=0,$$
--   and for all $\alpha\in\mathbb R$,
--   $$G(z+\alpha\Delta z)=(1-\alpha(1-\gamma))\,G(z),\qquad \langle x+\alpha\Delta x,s+\alpha\Delta s\rangle=(1-\alpha(1-\gamma))\langle x,s\rangle .$$
--
--   So a step of length $\alpha$ along the combined direction reduces the infeasibility residuals and the complementarity gap by the same factor. Iterating, $G(z^k)=\mu^kG(z^0)$ and $\langle x^k,s^k\rangle=\mu^k\vartheta$ when $\mu^0=1$: the algorithm needs no merit function to balance feasibility against optimality.
--
--   **Formalization Note** The first identity is printed on p. 353 as $\langle s,\Delta x\rangle+\langle x,\Delta s\rangle=0$. That is a misprint: the proof on the same page derives $-(1-\gamma)\langle x,s\rangle$, and together with $\langle\Delta x,\Delta s\rangle=0$ the printed version would give $\langle x+\alpha\Delta x,s+\alpha\Delta s\rangle=\langle x,s\rangle$, contradicting the last identity whenever $\gamma\ne1$. The repaired identity is stated (compare (12) of Lemma 2, the case $\gamma=0$, $\eta=0$). Inner products include the homogenizing coordinates, $\langle x,s\rangle=\langle\hat x,\hat s\rangle+\tau\kappa$. A single proper cone $\hat K$ stands for the paper's product of cones, and $W$ is any nonsingular linear map satisfying (8), not necessarily block diagonal; both are generalizations. The identities hold for every real $\gamma$; the hypothesis $\gamma>0$ is the paper's.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 353, Lemma 4 (first identity repaired per the proof on the same page)

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_ExpConeIPM_Corrector_HomogeneousModel
import Definitions.Def_ExpConeIPM_Corrector_SearchDirections

open scoped InnerProductSpace

namespace ExpConeIPM.Corrector

/-- **Lemma 4** (Dahl–Andersen, Math. Program. 194 (2022), p. 353), with the misprinted first
identity repaired. In the setting of Lemma 2, let `Δzᵃ` solve the affine system (11), let
`η := −½ F'''(x)[Δxᵃ, (F''(x))⁻¹Δsᵃ]` be the corrector (16) of the augmented barrier `F = F̂ − log τ`,
let `γ > 0`, and let `Δz` solve the combined system (18) with `μ = ⟨x, s⟩/ϑ`, `ϑ = ϑ̂ + 1`. Then
`⟨s, Δx⟩ + ⟨x, Δs⟩ = −(1 − γ)⟨x, s⟩` (printed as `= 0` on p. 353; the proof on the same page derives
`−(1 − γ)⟨x, s⟩`, and `= 0` contradicts the last identity), `⟨Δx, Δs⟩ = 0`, and for all `α ∈ ℝ`
`G(z + αΔz) = (1 − α(1 − γ)) G(z)` and `⟨x + αΔx, s + αΔs⟩ = (1 − α(1 − γ))⟨x, s⟩`. -/
theorem lemma_4 {n m : ℕ}
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
    (γ : ℝ) (hγ : 0 < γ)
    (dx ds : EuclideanSpace ℝ (Fin (n + 1))) (dy : EuclideanSpace ℝ (Fin m))
    (hd : IsCombinedDirection A b c Khat Fhat ϑhat x s y W
      (corrector (augBarrier Fhat) x dxa dsa) γ dx ds dy) :
    ⟪s, dx⟫_ℝ + ⟪x, ds⟫_ℝ = -(1 - γ) * ⟪x, s⟫_ℝ ∧ ⟪dx, ds⟫_ℝ = 0 ∧
      ∀ α : ℝ,
        residual A b c (x + α • dx) (s + α • ds) (y + α • dy) =
            (1 - α * (1 - γ)) • residual A b c x s y ∧
          ⟪x + α • dx, s + α • ds⟫_ℝ = (1 - α * (1 - γ)) * ⟪x, s⟫_ℝ := by sorry

end ExpConeIPM.Corrector
