-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_Supplement_theorem_4_1
-- name    : DirKKTBilevel.VP.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:24:51.271799+00:00
-- url     : https://prove2.me/theorems/aaf7c7ac-c2c6-4e74-8be1-e623a3d0b144
-- title:
--   Theorem 4.1 (companion theorem; not used in the proof of the goal; corrected: Ω_u ⊆ ℝᵐ) — directional Lipschitz continuity of the value function
-- statement:
--   Let $f,g$ be continuously differentiable and $u\in\mathbb R^n$.
--   1. If the restricted inf-compactness holds at $\bar x$ in direction $u$ with compact $\Omega_u\subseteq\mathbb R^m$ and $\mathcal F$ satisfies RS at each $(\bar x,y)\in\operatorname{gph}S$, then $V$ is directionally Lipschitz continuous at $\bar x$ in direction $u$.
--   2. If some $\bar y\in S(\bar x)$ has $S$ inner semi-continuous at $(\bar x,\bar y)$ in direction $u$ and $\mathcal F$ satisfies RS at $(\bar x,\bar y)$ in direction $u$, then $V$ is directionally Lipschitz continuous at $\bar x$ in direction $u$.
--   3. If (1) or (2) holds in direction $u=0$, then $V$ is Lipschitz at $\bar x$:
--   $$\exists L,\varepsilon>0:\quad |V(x)-V(x')|\le L\|x-x'\|\quad\forall x,x'\in\bar x+\varepsilon\mathbb B.$$
--   These are sufficient conditions for the directional Lipschitz hypothesis of Theorems 5.1 and 5.2 in terms of the lower-level data; part 1 assumes ordinary (non-directional) RS, as printed.
--
--   **Formalization Note** Directional Lipschitz continuity of the extended-real $V$ includes finiteness of $V$ on the directional neighbourhood; Lipschitz continuity at $\bar x$ is directional Lipschitz continuity in direction $0$, whose neighbourhood is the open ball.
--
--   Differences from the source:
--   - correction: Definition 4.1 (p. 13) places the compact set Ω_u in ℝⁿ → Ω : Set (E m), a set of lower-level variables in ℝᵐ; reason: Ω_u must meet S(x) ⊆ ℝᵐ, and the proofs of Lemma 4.2 (p. 16) and Proposition 4.3 (p. 17) take limits ỹ ∈ Ω_u of lower-level solutions; ℝⁿ is a dimension slip. No case is excluded.
--   - reading: Definitions 2.3 and 4.4 (pp. 6, 13) ask for y_k ∈ Φ(x̄ + t_k u_k) without saying for which k → dirLiminf and IsDirInnerSemicont require y_k ∈ Φ(x̄ + t_k u_k) for all sufficiently large k; reason: this is the Painlevé–Kuratowski convention the paper says it recovers at u = 0 (p. 6); requiring every k would force Φ(x) ≠ ∅ at every point x ≠ x̄, since any point is the first term of some admissible sequence, and the proofs (pp. 16, 18) only use large k.
--   - reading: standing assumption (§1, p. 2): F, f, g, G continuously differentiable → hypotheses ContDiff ℝ 1 on the data that the statement uses; reason: the standing smoothness of §1 governs §§4–5; the published base mission states it the same way.
--   - encoding: V real-valued wherever it is used; dist(y, ∅) = +∞ → V = valueFn is EReal-valued, directional Lipschitz continuity and differentiability carry finiteness of V; distances are the extended distance Metric.infEDist; reason: avoids the junk values of toReal and of Metric.infDist on the empty set; the published base model fixes the EReal value function.
--   - encoding: V is Lipschitz at x̄ → DirLipschitzAtEReal (valueFn f g) x 0; reason: V_{ε,δ}(0) is the open ε-ball, so this is Lipschitz continuity (with finiteness) on a ball around x̄.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 18, Theorem 4.1

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

namespace DirKKTBilevel.VP.Supplement

/-- Theorem 4.1, pp. 18–19: (i) if the restricted inf-compactness holds at `x̄` in direction `u`
with a compact set `Ω` and `𝓕` satisfies RS at each `(x̄, y) ∈ gph S`, then `V` is directionally
Lipschitz continuous at `x̄` in direction `u`; (ii) if some `ȳ ∈ S(x̄)` has `S` inner
semi-continuous at `(x̄, ȳ)` in direction `u` and `𝓕` satisfies RS at `(x̄, ȳ)` in direction `u`,
then `V` is directionally Lipschitz continuous at `x̄` in direction `u`. Furthermore, if (i) or (ii)
holds in direction `u = 0`, then `V` is Lipschitz at `x̄` (directional Lipschitz continuity in
direction `0` is Lipschitz continuity on an open ball around `x̄`). -/
theorem theorem_4_1 {n m p : ℕ} (f : Z n m → ℝ) (g : Z n m → E p)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x u : E n) :
    (∀ Ω : Set (E m), IsRestrInfCompactDir f g x u Ω →
        (∀ y ∈ solMap f g x, IsRSDir g x y 0) → DirLipschitzAtEReal (valueFn f g) x u) ∧
    (∀ y : E m, IsDirInnerSemicont f g x y u → IsRSDir g x y u →
        DirLipschitzAtEReal (valueFn f g) x u) ∧
    (((∃ Ω : Set (E m), IsRestrInfCompactDir f g x 0 Ω ∧ ∀ y ∈ solMap f g x, IsRSDir g x y 0) ∨
        (∃ y : E m, IsDirInnerSemicont f g x y 0 ∧ IsRSDir g x y 0)) →
      DirLipschitzAtEReal (valueFn f g) x 0) := by sorry

end DirKKTBilevel.VP.Supplement
