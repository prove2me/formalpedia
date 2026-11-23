-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_proposition_2_1
-- name    : DirKKTBilevel.VP.Supplement.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:31:36.179307+00:00
-- url     : https://prove2.me/theorems/9c36ea13-6841-4e36-8e75-2da797df679f
-- title:
--   Proposition 2.1 (used in the proof of Theorem 5.2) — directional Clarke subdifferential as an outer limit, and its sign rule
-- statement:
--   Let $\varphi:\mathbb R^n\to\mathbb R$ be directionally Lipschitz continuous at $\bar x$ in direction $u$. Then
--   $$\partial^c\varphi(\bar x;u)=\operatorname{co}\limsup_{x\xrightarrow{u}\bar x}\partial^c\varphi(x),\qquad \partial^c(-\varphi)(\bar x;u)=-\partial^c\varphi(\bar x;u),$$
--   where $\partial^c\varphi(x)=\partial^c\varphi(x;0)$ is the Clarke subdifferential. The sign rule is what allows Theorem 5.2 to pass from $\partial(-V)$ to $-\partial^cV$; it fails for the directional limiting subdifferential itself.
--
--   Differences from the source:
--   - encoding: t_k ↓ 0 → t k > 0 for all k and t → 0; reason: a decreasing subsequence can always be extracted; the same encoding as the published base mission.
--   - encoding: ϕ : ℝⁿ → ℝ and its subdifferentials → subdifferentials of the EReal coercion of ϕ; −∂ᶜϕ is the image under ξ ↦ −ξ; reason: the published dirSubdiff is defined for EReal-valued functions; finite values are unchanged.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 7, Proposition 2.1

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Proposition 2.1, p. 7: if `ϕ : ℝⁿ → ℝ` is directionally Lipschitz continuous at `x̄` in
direction `u`, then `∂ᶜϕ(x̄; u) = co limsup_{x →ᵤ x̄} ∂ᶜϕ(x)` and `∂ᶜ(−ϕ)(x̄; u) = −∂ᶜϕ(x̄; u)`,
where `∂ᶜϕ(x) = ∂ᶜϕ(x; 0)` is the Clarke subdifferential. -/
theorem proposition_2_1 {n : ℕ} (φ : E n → ℝ) (x u : E n) (hLip : DirLipschitzAt φ x u) :
    dirClarke (fun z => ((φ z : ℝ) : EReal)) x u =
        convexHull ℝ (dirLimsup (fun z => dirClarke (fun w => ((φ w : ℝ) : EReal)) z 0) x u) ∧
      dirClarke (fun z => ((-φ z : ℝ) : EReal)) x u =
        (fun ξ => -ξ) '' dirClarke (fun z => ((φ z : ℝ) : EReal)) x u := by sorry

end DirKKTBilevel.VP.Supplement
