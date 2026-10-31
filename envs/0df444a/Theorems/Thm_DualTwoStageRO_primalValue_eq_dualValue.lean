-- Prove2me | Theorems.Thm_DualTwoStageRO_primalValue_eq_dualValue
-- name    : DualTwoStageRO.primalValue_eq_dualValue
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:18.102974+00:00
-- url     : https://prove2.me/theorems/7c3460e0-c819-4e4d-a731-ed6a86500371
-- title:
--   Theorem 1, pointwise: the worst-case values of (1) and (6) coincide at each decision
-- statement:
--   Fix the data of (1)–(3) with $\mathcal U$ nonempty and every $f_i,g_i$ convex, and let $x$ be a decision for which the condition of Assumption 1 holds at every $\zeta\in\mathcal U$. Then
--
--   $$\sup_{\zeta\in\mathcal U}\ \inf_{y\in Y(x,\zeta)}\{f_0(x)+g_0(y)\}=\sup_{(u,v,w,z)\in\mathcal V}\ \inf_{\lambda\in\Lambda(x,v,w)}\Bigl\{\sum_{i=0}^{m_1}v_if_i(x)+d^\top\lambda-w^\top b(x)-\sum_{i=0}^{m_1}z_i\Bigr\}$$
--
--   in the extended reals, both sides possibly $\pm\infty$.
--
--   Both clauses of Theorem 1 follow from this identity at every $x\in\mathcal X$.
--
--   **Formalization Note** Assumption 1 is required only at $x$ (`Assumption1At`), and $x\in\mathcal X$ is not required.
--
--   Differences from the source:
--   - generalization: Assumption 1 for all x ∈ X, conclusion for x ∈ X → Assumption1At P x at one x, with x ∈ X not required; reason: Assumption 1 gives Assumption1At P x for each x ∈ X
--   - reading: v_i (g_i)^*(u_i/v_i), with the perspective defined on p.1795 only for real-valued functions → perspConj: v·g^*(u/v) for v > 0; at v = 0, 0 if u = 0 and +∞ otherwise (+∞ for v < 0); reason: Rockafellar's closure (p.67, cited by the page) of the perspective of g^* at v = 0 is the recession function of g^*, the support function of dom g = ℝ^{ny}; the reading 0·(anything) = 0 would enlarge V
--   - reading: strict inequality for all i = 1,…,m1 for which g_i is nonlinear → strict inequality for every i with g_i not affine (IsAffineFun); reason: an affine g_i is "linear" in the optimization sense; this is the weaker hypothesis, so the stronger theorem
--   - encoding: A^l ∈ ℝ^{m2×nζ}, b^l ∈ ℝ^{m2} "for all l = 0,…,nζ" (p.1794) → A0, b0 and Al l, bl l for l : Fin nx, i.e. l = 0,…,nx; reason: (2) sums over l = 1,…,nx, so nζ in the range is a slip
--   - encoding: infima and suprema of (1) and (6), possibly ±∞ → EReal values, inf over ∅ = ⊤, sup over ∅ = ⊥; ℝⁿ as Fin n → ℝ; the paper's i = 1,…,m1 as Fin m1 via Fin.succ; reason: Lean convention; same instances
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), Theorem 1, p.1796

import Mathlib
import Definitions.Def_DualTwoStageRO_dualValue
import Definitions.Def_DualTwoStageRO_Assumption1

namespace DualTwoStageRO

/-- **Theorem 1, pointwise: the worst-case values of (1) and (6) coincide at each decision.**
de Ruiter, Zhen, den Hertog, *Technical Note—Dual Approach for Two-Stage Robust Nonlinear
Optimization*, Operations Research 71(5), 2023, Theorem 1, p.1796.

Let `U` be nonempty, `f_i`, `g_i` convex, and let Assumption 1 hold at the decision `x`
(`Assumption1At P x`). Then `sup_{ζ∈U} inf_y {…}` of (1) equals `sup_{V} inf_λ {…}` of (6) at `x`,
in `EReal`.

**Formalization Note.** Assumption 1 is assumed only at `x`, and `x ∈ X` is not required. -/
theorem primalValue_eq_dualValue {nx ny nζ m1 m2 p : ℕ} (P : Problem nx ny nζ m1 m2 p)
    (hU : P.U.Nonempty) (hf : ∀ i, ConvexOn ℝ Set.univ (P.f i))
    (hg : ∀ i, ConvexOn ℝ Set.univ (P.g i)) (x : Fin nx → ℝ) (hA1 : Assumption1At P x) :
    primalValue P x = dualValue P x := by sorry

end DualTwoStageRO
