-- Prove2me | Theorems.Thm_DataDrivenRO_Marginal_support_UM
-- name    : DataDrivenRO.Marginal.support_UM
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:22:13.121753+00:00
-- url     : https://prove2.me/theorems/53840060-3ca2-47cb-b289-3139f9afd81d
-- title:
--   (29), p. 21 — δ*(v | 𝒰^M_ε) = Σᵢ max(vᵢû^(N−s+1)_i, vᵢû^(s)_i)
-- statement:
--   Let $d\ge1$, $0<\epsilon<1$, $0<\alpha<1$, $\hat{\mathbf u}^{(0)}\le\hat{\mathbf u}^{(N+1)}$, and suppose the index $s$ of (26) satisfies $N-s+1<s$. Then for every sample and every $\mathbf v\in\mathbb R^d$ the support function $\delta^*(\mathbf v\mid\mathcal U)=\sup_{\mathbf u\in\mathcal U}\mathbf v^T\mathbf u$ of the box (28) is
--   $$\delta^*(\mathbf v\mid\mathcal U^M_\epsilon)=\sum_{i=1}^d\max\big(v_i\hat u^{(N-s+1)}_i,\,v_i\hat u^{(s)}_i\big).$$
--
--   This closed form is Step 3 of the schema for $\mathcal U^M_\epsilon$, and Remark 12 uses it to separate over $\{(\mathbf v,t):\delta^*(\mathbf v\mid\mathcal U^M)\le t\}$.
--
--   **Formalization Note** The support function is the published `RobustMDP.Shared.supportFunction`, a real supremum; the box is nonempty and bounded under the hypotheses, so it is the genuine supremum.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 7, (29), p. 21; EC.1.5, p. ec5

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

open MeasureTheory

namespace DataDrivenRO.Marginal

/-- (29), p. 21: if `N − s + 1 < s`, the support function of `𝒰^M_ε` is
`δ*(v | 𝒰^M_ε) = ∑ᵢ max(vᵢ û^(N−s+1)_i, vᵢ û^(s)_i)`. -/
theorem support_UM {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (hα1 : α < 1) (lo hi : Fin d → ℝ) (hlohi : lo ≤ hi)
    (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) (S : Fin N → Fin d → ℝ) (v : Fin d → ℝ) :
    RobustMDP.Shared.supportFunction (UM S lo hi ε α) v =
      ∑ i, max (v i * uhat S lo hi i (N + 1 - sIndex N d ε α))
        (v i * uhat S lo hi i (sIndex N d ε α)) := by sorry

end DataDrivenRO.Marginal
