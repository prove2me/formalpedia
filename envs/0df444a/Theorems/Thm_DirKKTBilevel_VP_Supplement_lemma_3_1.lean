-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_lemma_3_1
-- name    : DirKKTBilevel.VP.Supplement.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:32:03.481843+00:00
-- url     : https://prove2.me/theorems/e907d524-e36d-47a6-8041-1e3b281779ac
-- title:
--   Lemma 3.1 (used in the proof of Theorem 5.2) — directional MSCQ implies directional calmness of (P)
-- statement:
--   Consider problem (P): minimize $\phi(z)$ subject to $\varphi(z)\le0$, with $\phi:X\to\mathbb R$ and $\varphi:X\to\mathbb R^q$. Let $\bar z$ solve (P) (locally: $\bar z$ is a local minimizer of (P)), let $\phi$ be directionally Lipschitz continuous at $\bar z$ in direction $u$, and let the system $\varphi(z)\le0$ satisfy the directional MSCQ at $\bar z$ in direction $u$. Then (P) is calm at $\bar z$ in direction $u$: there are $\varepsilon,\delta,\rho>0$ with
--   $$\phi(z)-\phi(\bar z)+\rho\|\alpha\|\ge0$$
--   for all $\alpha\in\varepsilon\mathbb B$ and $z\in\bar z+V_{\varepsilon,\delta}(u)$ with $\varphi(z)+\alpha\le0$ (Definition 3.1). Combined with Proposition 3.1 it turns quasi-normality into the calmness hypothesis of Theorems 3.1 and 5.1.
--
--   Differences from the source:
--   - generalization: ℝⁿ → a finite-dimensional real inner product space X; reason: every such X is linearly isometric to some ℝⁿ, so the statement specializes to the source exactly; the published Theorem 3.1 uses the same X so that the results apply on the product space of (VP).
--   - reading: 'Let z̄ solve (P)' → IsLocalMinOn obj {w | con w ≤ 0} z̄ (a local minimizer; feasibility of z̄ is part of the directional MSCQ hypothesis); reason: the proof of Theorem 5.2 (p. 25) applies the lemma at a local minimizer of (BP), and Theorem 3.1, which the lemma feeds, is for local minimizers; the local reading contains the global one, and the proof goes through with a smaller ε, since the feasible point z̃ near z lies within κ‖α‖ of z and hence near z̄.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 8, Lemma 3.1

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Lemma 3.1, p. 8: let `z̄` solve (P) `min obj(z)` s.t. `con(z) ≤ 0` (a local minimizer, the
sense in which the lemma is applied in the proof of Theorem 5.2), let `obj` be directionally
Lipschitz continuous at `z̄` in direction `u`, and let `con(z) ≤ 0` satisfy the directional MSCQ at
`z̄` in direction `u` (which includes feasibility of `z̄`). Then (P) is calm at `z̄` in direction
`u`. -/
theorem lemma_3_1 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X)
    (hsol : IsLocalMinOn obj {w | ∀ j, con w j ≤ 0} z)
    (hLip : DirLipschitzAt obj z u) (hMSCQ : DirMSCQ con z u) :
    IsCalmDir obj con z u := by sorry

end DirKKTBilevel.VP.Supplement
