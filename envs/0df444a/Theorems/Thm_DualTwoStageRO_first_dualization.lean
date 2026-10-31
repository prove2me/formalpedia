-- Prove2me | Theorems.Thm_DualTwoStageRO_first_dualization
-- name    : DualTwoStageRO.first_dualization
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:01.064168+00:00
-- url     : https://prove2.me/theorems/d5c52056-0884-436f-9d60-b23c1beb446b
-- title:
--   First dualization, over the adjustable variables (abstract, p.1794)
-- statement:
--   Fix the data of (1)–(3) with every $g_i$ convex, a decision $x$ and a scenario $\zeta$, and suppose some $y$ satisfies the constraints of (1) at $(x,\zeta)$, strictly for every $i=1,\dots,m_1$ with $g_i$ not affine. Then the inner value of (1) is
--
--   $$\inf_{y\in Y(x,\zeta)}\{f_0(x)+g_0(y)\}=\sup_{(u,v,w,z)\in\mathcal V}\Bigl\{\sum_{i=0}^{m_1}v_if_i(x)+\sum_{i=1}^{m_1}v_i\,\zeta^\top F_{i\cdot}(x)+w^\top\bigl(A(x)\zeta-b(x)\bigr)-\sum_{i=0}^{m_1}z_i\Bigr\}$$
--
--   in the extended reals.
--
--   This is the dualization over the adjustable variable $y$: the right-hand side is linear in $\zeta$, and the nonlinear functions $g_i$ appear only in the set $\mathcal V$.
--
--   **Formalization Note** $\zeta$ need not lie in $\mathcal U$; only the condition of Assumption 1 at this pair is assumed (`RecourseAt`).
--
--   Differences from the source:
--   - generalization: Assumption 1 for all x ∈ X, ζ ∈ U, with f_i convex → the recourse condition at the single pair (x, ζ), ζ arbitrary, f_i arbitrary; reason: Assumption 1 gives RecourseAt P x ζ for every x ∈ X, ζ ∈ U, and f_i(x) enter only as constants
--   - reading: v_i (g_i)^*(u_i/v_i), with the perspective defined on p.1795 only for real-valued functions → perspConj: v·g^*(u/v) for v > 0; at v = 0, 0 if u = 0 and +∞ otherwise (+∞ for v < 0); reason: Rockafellar's closure (p.67, cited by the page) of the perspective of g^* at v = 0 is the recession function of g^*, the support function of dom g = ℝ^{ny}; the reading 0·(anything) = 0 would enlarge V
--   - reading: strict inequality for all i = 1,…,m1 for which g_i is nonlinear → strict inequality for every i with g_i not affine (IsAffineFun); reason: an affine g_i is "linear" in the optimization sense; this is the weaker hypothesis, so the stronger theorem
--   - encoding: A^l ∈ ℝ^{m2×nζ}, b^l ∈ ℝ^{m2} "for all l = 0,…,nζ" (p.1794) → A0, b0 and Al l, bl l for l : Fin nx, i.e. l = 0,…,nx; reason: (2) sums over l = 1,…,nx, so nζ in the range is a slip
--   - encoding: infima and suprema of (1) and (6), possibly ±∞ → EReal values, inf over ∅ = ⊤, sup over ∅ = ⊥; ℝⁿ as Fin n → ℝ; the paper's i = 1,…,m1 as Fin m1 via Fin.succ; reason: Lean convention; same instances
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), abstract, p.1794 ("first dualizing over the adjustable variables"); Assumption 1, p.1795; V, p.1796

import Mathlib
import Definitions.Def_DualTwoStageRO_dualSet
import Definitions.Def_DualTwoStageRO_Assumption1

namespace DualTwoStageRO

open Matrix

/-- **First dualization, over the adjustable variables.**
de Ruiter, Zhen, den Hertog, *Technical Note—Dual Approach for Two-Stage Robust Nonlinear
Optimization*, Operations Research 71(5), 2023, abstract, p.1794: "The reformulation is obtained by
first dualizing over the adjustable variables and then over the uncertain parameters."

For a here-and-now decision `x` and a scenario `ζ` at which the recourse condition of Assumption 1
holds (some `y` feasible for (1), strictly for every constraint with a non-affine `g_i`), with every
`g_i` convex, the inner value of (1) equals
`sup_{(u,v,w,z)∈V} [ Σ_{i=0}^{m1} v_i f_i(x) + Σ_{i=1}^{m1} v_i ζ⊤F_i·(x) + w⊤(A(x)ζ − b(x))
− Σ_{i=0}^{m1} z_i ]`, in `EReal`.

**Formalization Note.** `ζ` is not required to lie in `U`, and only `RecourseAt P x ζ` (Assumption 1
at this one pair) is assumed. -/
theorem first_dualization {nx ny nζ m1 m2 p : ℕ} (P : Problem nx ny nζ m1 m2 p)
    (hg : ∀ i, ConvexOn ℝ Set.univ (P.g i)) (x : Fin nx → ℝ) (ζ : Fin nζ → ℝ)
    (hrec : RecourseAt P x ζ) :
    innerValue P x ζ =
      ⨆ q ∈ dualSet P,
        ((∑ i, q.v i * P.f i x + ∑ i : Fin m1, q.v i.succ * (ζ ⬝ᵥ fun j => P.F i j x) +
            q.w ⬝ᵥ (P.A x *ᵥ ζ - P.b x) - ∑ i, q.z i : ℝ) : EReal) := by sorry

end DualTwoStageRO
