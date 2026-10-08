-- Prove2me | Theorems.Thm_AssortSearch_SearchQC_D_K_pos_increasing
-- name    : AssortSearch.SearchQC.D_K_pos_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:09.33646+00:00
-- url     : https://prove2.me/theorems/8e942b6e-5bba-489a-ad97-92de5f3701eb
-- title:
--   Proof of Theorem 5: $D$ and $K$ are positive and increasing, and $K/D$ is increasing
-- statement:
--   Let $\lambda>0$ and $V_S>0$, and for $v_j\ge0$ put
--   $$D(v_j)=e^{\lambda(v_j+V_S)}-1+\frac{\lambda v_j}{V_S}(v_j+V_S),\qquad K(v_j)=e^{\lambda(v_j+V_S)}-1-\lambda(v_j+V_S).$$
--   Then:
--   1. $D(v_j)>0$ and $K(v_j)>0$ for every $v_j\ge0$;
--   2. $D$ and $K$ are strictly increasing on $[0,\infty)$;
--   3. the ratio $K(v_j)/D(v_j)$ is strictly increasing on $[0,\infty)$.
--
--   The paper asserts these facts without proof. They are used in Case (1) of the proof of Theorem 5, where $h^{si\prime}$ is written as a positive term times an increasing one.
--
--   **Formalization Note** The paper says "increasing"; the strict form is stated, which holds for all $\lambda>0$, $V_S>0$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), pp. 15-16 (PDF 17-18), proof of Theorem 5

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_ProofTerms

namespace AssortSearch.SearchQC

/-- pp. 15–16: for `λ > 0` and `V_S > 0`, `D` and `K` are positive and increasing on
`v_j ∈ [0, ∞)`, and so is `K/D`. -/
theorem D_K_pos_increasing (lam VS : ℝ) (hlam : 0 < lam) (hVS : 0 < VS) :
    (∀ x ∈ Set.Ici (0 : ℝ), 0 < Dfn lam VS x ∧ 0 < Kfn lam VS x) ∧
      StrictMonoOn (Dfn lam VS) (Set.Ici 0) ∧
      StrictMonoOn (Kfn lam VS) (Set.Ici 0) ∧
      StrictMonoOn (fun x => Kfn lam VS x / Dfn lam VS x) (Set.Ici 0) := by sorry

end AssortSearch.SearchQC
