-- Prove2me | Theorems.Thm_DistTransform_Distortion_claims_i_ii
-- name    : DistTransform.Distortion.claims_i_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:26.148992+00:00
-- url     : https://prove2.me/theorems/a993e26d-14b4-4126-8353-08be4f245be8
-- title:
--   Proof of Theorem 1, p. 7, claims (i)–(ii) — q_p^T is monotone and commutes with shape transforms
-- statement:
--   Let $\mathcal M=\mathcal M_0$ or $\mathcal M=\mathcal M_\infty$, let $T$ map $\mathcal M$ into $\mathcal M$, and suppose $T$ is monotone and commutes with shape transforms on $\mathcal M$. Fix $p\in(0,1)$ and define $q_p^T(F)=q_p(T(F))=(T(F))^{-1}(p)$, the left $p$-quantile of $T(F)$. Then
--
--   1. $q_p^T(F)\le q_p^T(G)$ for all $F,G\in\mathcal M$ with $F\preceq_{\mathrm{st}}G$;
--   2. for every strictly increasing continuous $\varphi$ with $\varphi(\mathbb R)=\mathbb R$ and every $F\in\mathcal M$,
--   $$
--   q_p^T\big(T^{[\varphi]}(F)\big)=\varphi\big(q_p^T(F)\big).
--   $$
--
--   These two properties are what allow the proof of Theorem 1 to apply Chambers' axiomatization of quantiles to $q_p^T$.
--
--   **Formalization Note** The left quantile is a real `sInf`, which is the paper's finite quantile at every level $p\in(0,1)$.
-- source:
--   Liu, Schied and Wang, Distributional transforms, probability distortions, and their applications, SSRN 3419388 (version of March 19, 2020), pp. 6–7, claims (i)–(ii) in the proof of Theorem 1

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace DistTransform.Distortion

/-- Proof of Theorem 1, p. 7, claims (i)–(ii): for `p ∈ (0, 1)` the functional
`q_p^T(F) = q_p(T(F))` (left `p`-quantile of `T(F)`) is monotone in `⩽st` and satisfies
`q_p^T(T^[φ](F)) = φ(q_p^T(F))` for every shape transform `φ`. -/
theorem claims_i_ii (M : Set (ProbabilityMeasure ℝ)) (hM : M = Set.univ ∨ M = Minf)
    (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ) (hT : Set.MapsTo T M M)
    (hmono : IsMonotoneT M T) (hcomm : CommutesWithShape M T)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ F ∈ M, ∀ G ∈ M, StLE F G → leftQuantile (T F) p ≤ leftQuantile (T G) p) ∧
      (∀ φ : ℝ ≃o ℝ, ∀ F ∈ M, leftQuantile (T (shape φ F)) p = φ (leftQuantile (T F) p)) := by sorry

end DistTransform.Distortion
