-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_proposition_3_1
-- name    : DirKKTBilevel.VP.Supplement.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:32:42.754474+00:00
-- url     : https://prove2.me/theorems/c32fd1d5-8785-499b-9cdd-402d67f8e942
-- title:
--   Proposition 3.1 (used in the proof of Theorem 5.2) — directional quasi-normality implies directional MSCQ
-- statement:
--   Let $\varphi:X\to\mathbb R^q$ with $\varphi(\bar z)\le0$ be directionally Lipschitz continuous and directionally differentiable at $\bar z$ in direction $u$, with $d=\varphi'(\bar z;u)$, and let $u\in L(\bar z)$, i.e. $d_j\le0$ for every active index $j$. If the directional quasi-normality holds at $\bar z$ in direction $u$ for $\varphi(z)\le0$, then $\varphi(z)\le0$ satisfies the directional MSCQ at $\bar z$ in direction $u$:
--   $$\operatorname{dist}(z,\varphi^{-1}(\mathbb R^q_-))\le\kappa\|\varphi_+(z)\|\qquad\forall z\in\bar z+V_{\varepsilon,\delta}(u).$$
--   This is the constraint-qualification step of Theorem 5.2.
--
--   Differences from the source:
--   - generalization: ℝⁿ → a finite-dimensional real inner product space X; reason: every such X is linearly isometric to some ℝⁿ, so the statement specializes to the source exactly; the published Theorem 3.1 uses the same X so that the results apply on the product space of (VP).
--   - encoding: λ ⊥ w for vectors → Σ_i λ_i w_i = 0; reason: the inner product of ℝᵖ; the same encoding as the published base mission.
--   - encoding: t_k ↓ 0 → t k > 0 for all k and t → 0; reason: a decreasing subsequence can always be extracted; the same encoding as the published base mission.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 9, Proposition 3.1

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Proposition 3.1, p. 9: let `con(z̄) ≤ 0`, let `con` be directionally Lipschitz and directionally
differentiable at `z̄` in direction `u` with `d = con'(z̄; u)`, and let `u ∈ L(z̄)` (`d_j ≤ 0` for
every active `j`). If the directional quasi-normality holds at `z̄` in direction `u`, then
`con(z) ≤ 0` satisfies the directional MSCQ at `z̄` in direction `u`. -/
theorem proposition_3_1 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {q : ℕ} (con : X → E q) (z u : X) (d : E q)
    (hfeas : ∀ j, con z j ≤ 0) (hLip : DirLipschitzAt con z u) (hdir : HasDirDerivAt con z u d)
    (hlin : ∀ j ∈ activeSet con z, d j ≤ 0) (hQN : DirQuasiNormal con z u d) :
    DirMSCQ con z u := by sorry

end DirKKTBilevel.VP.Supplement
