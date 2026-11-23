-- Prove2me | Theorems.Thm_ConeLifts_Factorization_Supplement_symmetric_factorization_theorem
-- name    : ConeLifts.Factorization.Supplement.symmetric_factorization_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:48:36.2392+00:00
-- url     : https://prove2.me/theorems/65d0a9fd-db65-4c46-9235-1cd3ec4c502a
-- title:
--   Theorem 2.12 (corrected: n ≥ 1, compact G and continuous ϕ ↦ f_ϕ in the forward half) — symmetric lifts and symmetric slack factorizations
-- statement:
--   Let $C \subseteq \mathbb R^n$ be a convex body (compact, convex, with the origin in its interior) and $K \subseteq \mathbb R^m$ a full-dimensional closed convex cone. Let $G \subseteq \mathrm{GL}_n(\mathbb R)$ be a group acting on the extreme points $\operatorname{ext}(C)$ and $H \subseteq \mathrm{GL}_m(\mathbb R)$ a group acting on $K$. Then:
--
--   1. if $n \ge 1$, $G$ is compact, and $C$ has a proper $(G,H)$-symmetric $K$-lift $C = \pi(K \cap L)$ (that is, $L$ meets the interior of $K$) whose homomorphism $\varphi \mapsto f_\varphi$ is continuous, then the slack operator $S_C$ has a $(G,H)$-symmetric $K$-factorization;
--   2. if $S_C$ has a $(G,H)$-symmetric $K$-factorization, then $C$ has a $(G,H)$-symmetric $K$-lift.
--
--   $$
--   \text{proper symmetric lift} \;\Longrightarrow\; \text{symmetric factorization} \;\Longrightarrow\; \text{symmetric lift}.
--   $$
--
--   This is the symmetric version of the factorization theorem (Theorem 2.4): the correspondence between lifts and slack factorizations respects any group of symmetries of the body.
--
--   **Formalization Note** Groups are subgroups of `GL (Fin n) ℝ` with its standard topology; the homomorphism of the conclusion is a fresh existential. The lift of the converse need not be proper.
--
--   Differences from the source:
--   - correction: no dimension condition → the first part assumes $n \ge 1$; reason: for $n = 0$, $C = \{0\} = \mathbb R^0$ has a proper $\mathbb R^m$-lift but $(\mathbb R^m)^* = \{0\}$ cannot factor $S_C = 1$, the same exception as the published Theorem 2.4; the converse keeps $n = 0$
--   - correction: G is asserted compact (p. 7) and the proof averages over the Haar measure of the stabiliser $G_{x_0}$ → the first part assumes $G$ compact and $\varphi \mapsto f_\varphi$ continuous; reason: an arbitrary subgroup of $\mathrm{GL}_n$ acting on $\operatorname{ext}(C)$ need not be closed, and the Haar integral of $f_\varphi(A'(x_0))$ needs a measurable integrand; excluded are non-closed groups and discontinuous homomorphisms, which the paper's proof does not cover
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 8, Theorem 2.12

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Factorization_IsClosedConvexCone
import Definitions.Def_ConeLifts_Factorization_Supplement_IsSymmetricLift
import Definitions.Def_ConeLifts_Factorization_Supplement_IsSymmetricFactorization

namespace ConeLifts.Factorization.Supplement

/-- **Theorem 2.12** of Gouveia, Parrilo & Thomas, *Lifts of Convex Sets and Cone
Factorizations*, arXiv:1111.3164v2, p. 8: "If C has a proper (G, H)-symmetric K-lift then S_C has
a (G, H)-symmetric K-factorization. Conversely, if S_C has a (G, H)-symmetric K-factorization
then C has a (G, H)-symmetric K-lift."

Setting (Definition 2.10, p. 7): `C ⊆ ℝⁿ` a convex body, `K ⊆ ℝᵐ` a full-dimensional closed
convex cone, `G ⊆ GLₙ(ℝ)` a subgroup acting on `ext(C)`, `H ⊆ GLₘ(ℝ)` a subgroup acting on `K`.

Recorded repairs, forward half only: (i) `1 ≤ n`, as in Theorem 2.4 (for `n = 0`, `C = {0} = ℝ⁰`
has a proper `ℝᵐ`-lift while `(ℝᵐ)* = {0}` cannot factor `S_C = 1`); (ii) `G` is compact in
`GLₙ(ℝ)` and the homomorphism `ϕ ↦ f_ϕ` of the given lift is continuous. The paper asserts
(p. 7) that every such `G` is compact and its proof averages over the Haar measure of the
stabiliser `G_{x₀}` (p. 8), which needs both. The converse carries neither premise. The
homomorphisms of hypothesis and conclusion are separate existentials. -/
theorem symmetric_factorization_theorem {n m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : ConeLifts.Factorization.IsConvexBody C)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : ConeLifts.Factorization.IsClosedConvexCone K)
    (hKint : (interior K).Nonempty)
    (G : Subgroup (GL (Fin n) ℝ)) (hG : ActsOnExtremePoints G C)
    (H : Subgroup (GL (Fin m) ℝ)) (hH : ActsOnCone H K) :
    (1 ≤ n → IsCompact (G : Set (GL (Fin n) ℝ)) →
      (∃ (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)))
        (π : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) (f : G →* H),
        IsSymmetricLift G H K C L π f ∧
          (interior K ∩ (L : Set (EuclideanSpace ℝ (Fin m)))).Nonempty ∧ Continuous f) →
      HasSymmetricFactorization G H K C) ∧
    (HasSymmetricFactorization G H K C → HasSymmetricLift G H K C) := by sorry

end ConeLifts.Factorization.Supplement
