-- Prove2me | Theorems.Thm_DualTwoStageRO_theorem_1
-- name    : DualTwoStageRO.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:03.749989+00:00
-- url     : https://prove2.me/theorems/5ab38494-76f7-48c7-b49d-b2a9154da9f8
-- title:
--   Theorem 1 (Dual Formulation) — same feasible decisions and same optimal value
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^{n_x}$, let $f_i,g_i$ ($i=0,\dots,m_1$) be convex and $F_{ij}$ real-valued, let $A(x),b(x)$ be affine as in (2), and let $\mathcal U=\{\zeta\ge0:D\zeta=d\}$ be a nonempty polyhedral set as in (3). Assume Assumption 1 (relatively complete recourse, strict for the constraints with nonlinear $g_i$). Write
--
--   $$\Phi(x)=\sup_{\zeta\in\mathcal U}\ \inf_y\bigl\{f_0(x)+g_0(y)\ \big|\ \zeta^\top F_{i\cdot}(x)+f_i(x)+g_i(y)\le0,\ i=1,\dots,m_1,\ A(x)\zeta+By=b(x)\bigr\}$$
--
--   for the worst-case value of $x$ in (1), and
--
--   $$\Psi(x)=\sup_{(u,v,w,z)\in\mathcal V}\ \inf_\lambda\Bigl\{\sum_{i=0}^{m_1}v_if_i(x)+d^\top\lambda-w^\top b(x)-\sum_{i=0}^{m_1}z_i\ \Big|\ \sum_{k=1}^pD_{kj}\lambda_k\ge w^\top A_{\cdot j}(x)+\sum_{i=1}^{m_1}v_iF_{ij}(x),\ j=1,\dots,n_\zeta\Bigr\}$$
--
--   for that in the dualized model (6), with
--
--   $$\mathcal V=\Bigl\{(u,v,w,z):\ v\ge0,\ v_0=1,\ v_i(g_i)^*\Bigl(\frac{u_i}{v_i}\Bigr)\le z_i,\ i=0,\dots,m_1,\ \sum_{i=0}^{m_1}u_i=-B^\top w\Bigr\}.$$
--
--   Then:
--
--   1. a here-and-now decision $x\in\mathcal X$ is feasible for (1) if and only if it is feasible for (6), i.e. $\Phi(x)<+\infty\iff\Psi(x)<+\infty$;
--   2. the infimum of (1) coincides with that of (6): $\inf_{x\in\mathcal X}\Phi(x)=\inf_{x\in\mathcal X}\Psi(x)$.
--
--   In (6) the adjustable variable $\lambda$ enters linearly, so every method for adjustable robust linear problems applies to it.
--
--   **Formalization Note** Values are in `EReal`. No dimension is assumed positive, $\mathcal U$ may be unbounded, and $\mathcal X$ is an arbitrary set.
--
--   Differences from the source:
--   - reading: "x is feasible for (1)" / "for (6)", not defined for a min–sup–min → primalValue P x < ⊤ / dualValue P x < ⊤ (the worst-case value is below +∞); reason: the scenario-wise reading (a y for every ζ ∈ U, a λ for every V-point) makes the theorem false: nx = nζ = ny = m2 = p = 1, m1 = 0, D = 0, d = 0, f0 = 0, g0(y) = −y, A ≡ 1, B = 1, b ≡ 0 satisfies every assumption, every x is scenario-wise feasible for (1), but V = {u0 = −1, v0 = 1, w = 1, z0 ≥ 0} and (6)'s λ-constraint reads 0 ≥ 1
--   - reading: v_i (g_i)^*(u_i/v_i), with the perspective defined on p.1795 only for real-valued functions → perspConj: v·g^*(u/v) for v > 0; at v = 0, 0 if u = 0 and +∞ otherwise (+∞ for v < 0); reason: Rockafellar's closure (p.67, cited by the page) of the perspective of g^* at v = 0 is the recession function of g^*, the support function of dom g = ℝ^{ny}; the reading 0·(anything) = 0 would enlarge V
--   - reading: strict inequality for all i = 1,…,m1 for which g_i is nonlinear → strict inequality for every i with g_i not affine (IsAffineFun); reason: an affine g_i is "linear" in the optimization sense; this is the weaker hypothesis, so the stronger theorem
--   - encoding: A^l ∈ ℝ^{m2×nζ}, b^l ∈ ℝ^{m2} "for all l = 0,…,nζ" (p.1794) → A0, b0 and Al l, bl l for l : Fin nx, i.e. l = 0,…,nx; reason: (2) sums over l = 1,…,nx, so nζ in the range is a slip
--   - encoding: infima and suprema of (1) and (6), possibly ±∞ → EReal values, inf over ∅ = ⊤, sup over ∅ = ⊥; ℝⁿ as Fin n → ℝ; the paper's i = 1,…,m1 as Fin m1 via Fin.succ; reason: Lean convention; same instances
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), Theorem 1 (Dual Formulation), p.1796; problem (1)–(3), p.1794; Assumption 1, p.1795

import Mathlib
import Definitions.Def_DualTwoStageRO_dualValue
import Definitions.Def_DualTwoStageRO_Assumption1

namespace DualTwoStageRO

/-- **Theorem 1 (Dual Formulation).**
de Ruiter, Zhen, den Hertog, *Technical Note—Dual Approach for Two-Stage Robust Nonlinear
Optimization*, Operations Research 71(5), 2023, Theorem 1, p.1796: "Let U be a polyhedral set as in
(3) and assume that Assumption 1 holds. The here and now decision x is feasible for (1) if and only
if x is feasible for the following dualized model: (6) … Moreover, the infimum of (1) coincides with
that of (6)."

**Formalization Note.** The data are those of (1)–(3) (`Problem`: affine `A(x)`, `b(x)`), with `U`
nonempty and `f_i`, `g_i` convex for `i = 0,…,m1`. All values are in `EReal`. "x is feasible for (1)"
is `primalValue P x < ⊤` and "x is feasible for (6)" is `dualValue P x < ⊤`. No dimension is assumed
positive, `U` may be unbounded, and `X` is an arbitrary set. -/
theorem theorem_1 {nx ny nζ m1 m2 p : ℕ} (P : Problem nx ny nζ m1 m2 p)
    (hU : P.U.Nonempty) (hf : ∀ i, ConvexOn ℝ Set.univ (P.f i))
    (hg : ∀ i, ConvexOn ℝ Set.univ (P.g i)) (hA1 : Assumption1 P) :
    (∀ x ∈ P.X, (primalValue P x < ⊤ ↔ dualValue P x < ⊤)) ∧
      (⨅ x ∈ P.X, primalValue P x) = ⨅ x ∈ P.X, dualValue P x := by sorry

end DualTwoStageRO
