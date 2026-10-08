-- Prove2me | Theorems.Thm_ExpConeIPM_Corrector_barrier_sum_tau
-- name    : ExpConeIPM.Corrector.barrier_sum_tau
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:29.244271+00:00
-- url     : https://prove2.me/theorems/053d751d-ec2d-44dc-bba0-c9df328866b2
-- title:
--   §2 sum rule for the homogenizing block: $\hat F(\hat x)-\log\tau$ is a $(\hat\vartheta+1)$-LHSCB for $\hat K\times\mathbb R_+$
-- statement:
--   Let $\hat K\subseteq\mathbb R^n$ be a proper cone and let $\hat F$ be a $\hat\vartheta$-logarithmically homogeneous self-concordant barrier for $\hat K$. Then the augmented cone
--   $$K=\hat K\times\mathbb R_+=\{(\hat x,\tau)\in\mathbb R^{n+1}:\hat x\in\hat K,\ \tau\ge0\}$$
--   is a proper cone, and
--   $$F(\hat x,\tau)=\hat F(\hat x)-\log\tau$$
--   is a $(\hat\vartheta+1)$-logarithmically homogeneous self-concordant barrier for $K$.
--
--   The paper states the general sum rule: if $F_1$ and $F_2$ are $\vartheta_1$- and $\vartheta_2$-self-concordant barriers for $K_1$ and $K_2$, then $F_1(x_1)+F_2(x_2)$ is a $(\vartheta_1+\vartheta_2)$-self-concordant barrier for $K_1\times K_2$; on p. 347 it applies it with $K_{k+1}=\mathbb R_+$, $F_{k+1}=-\log$, $\vartheta_{k+1}=1$ to build the barrier $F$ and the complexity $\vartheta$ of the homogeneous model. This theorem is that application. It is what lets the §2 identities be used for the augmented barrier in Lemmas 3 and 4.
--
--   **Formalization Note** This is the paper's sum rule specialized to $K_2=\mathbb R_+$, $F_2=-\log$, $\vartheta_2=1$ (p. 347). The barrier notion is the published `IsLogHomBarrier`; the augmented space is `EuclideanSpace ℝ (Fin (n + 1))` with $\tau$ the last coordinate.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 345 (sum rule) applied as on pp. 347–348 (K_{k+1} := ℝ₊, F_{k+1} := −log, ϑ_{k+1} = 1)

import Mathlib
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_ExpConeIPM_Corrector_HomogeneousModel

namespace ExpConeIPM.Corrector

/-- **§2 sum rule, applied to the homogenizing block** (Dahl–Andersen, Math. Program. 194 (2022),
p. 345 with p. 347–348). If `K̂ ⊆ ℝⁿ` is a proper cone and `F̂` is a `ϑ̂`-LHSCB for `K̂`, then the
augmented cone `K = K̂ × ℝ₊ ⊆ ℝⁿ⁺¹` is proper and `F(x̂, τ) = F̂(x̂) − log τ` is a `(ϑ̂ + 1)`-LHSCB for
`K`. This is the paper's sum rule for `K₁ × K₂` specialized to `K₂ = ℝ₊`, `F₂ = −log`, `ϑ₂ = 1`. -/
theorem barrier_sum_tau {n : ℕ} (Khat : Set (EuclideanSpace ℝ (Fin n)))
    (Fhat : EuclideanSpace ℝ (Fin n) → ℝ) (ϑhat : ℝ)
    (hK : SelfScaledIPM.ShortStep.IsProperCone Khat)
    (hF : SelfScaledIPM.ShortStep.IsLogHomBarrier Khat Fhat ϑhat) :
    SelfScaledIPM.ShortStep.IsProperCone (augCone Khat) ∧
      SelfScaledIPM.ShortStep.IsLogHomBarrier (augCone Khat) (augBarrier Fhat) (augParam ϑhat) := by sorry

end ExpConeIPM.Corrector
