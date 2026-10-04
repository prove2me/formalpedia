-- Prove2me | Theorems.Thm_EkelandVP_Constraints_lemma_3_2
-- name    : EkelandVP.Constraints.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:52:01.063638+00:00
-- url     : https://prove2.me/theorems/cd2ef7d3-bd43-43b1-aef3-ee50234db59b
-- title:
--   Lemma 3.2, p. 331 — at an Ekeland point, ⟨F′(v), h⟩ ≥ −ε‖h‖ for every linearized feasible direction h
-- statement:
--   Let $V$ be a real Banach space, $F:V\to\mathbb R$ Fréchet-differentiable and $G_1,\dots,G_m:V\to\mathbb R$ of class $C^1$, with feasible set $\mathcal C$ (3.2) and saturated set $I(v)$ (3.3). Let $\varepsilon\in\mathbb R$ and let $v\in\mathcal C$ be a point with property (3.12),
--   $$F(w)\ge F(v)-\varepsilon\|w-v\|\qquad\text{for all } w\in\mathcal C,$$
--   at which $\big(G_i'(v)\big)_{i\in I(v)}$ is linearly independent. Let $h\in V$ satisfy
--   $$\langle G_i'(v),h\rangle=0\ \ (1\le i\le p), \tag{3.13}$$
--   $$\langle G_i'(v),h\rangle\ge 0\ \ (i\in\{p+1,\dots,m\}\cap I(v)). \tag{3.14}$$
--   Then
--   $$\langle F'(v),h\rangle\ge-\varepsilon\|h\|. \tag{3.15}$$
--
--   In the paper $v$ is the point $v_\varepsilon$ produced by the variational principle; combined with Lemma 3.3 this gives the approximate multiplier rule of Theorem 3.1.
--
--   **Formalization Note.** The lemma is stated for any feasible $v$ with property (3.12), not only for the specific $v_\varepsilon$ of the proof, and with regularity only at $v$; both are what the page's proof uses. $\langle F'(v),h\rangle$ is `fderiv ℝ F v h`. The page writes $F'(v)$ in (3.15) for $F'(v_\varepsilon)$. Constraint $i$ of the page is Lean index $i-1$.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 331, §3, Lemma 3.2, (3.13)–(3.15)

import Mathlib
import Definitions.Def_EkelandVP_Constraints_feasibleSet

namespace EkelandVP.Constraints

/-- Ekeland (1974), Lemma 3.2, p. 331: let `v` be a feasible point with property (3.12),
`F(w) ≥ F(v) - ε ‖w - v‖` for all feasible `w`, at which the saturated constraint derivatives are
linearly independent ((3.4) at `v`). If `h` satisfies (3.13) and (3.14), then
`⟨F'(v), h⟩ ≥ -ε ‖h‖` (3.15). -/
theorem lemma_3_2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {m : ℕ} (p : ℕ) (F : V → ℝ) (G : Fin m → V → ℝ)
    (hF : Differentiable ℝ F) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (ε : ℝ) (v : V) (hv : v ∈ feasibleSet p G)
    (hli : LinearIndependent ℝ (fun i : {i : Fin m // G i v = 0} => fderiv ℝ (G i) v))
    (h12 : ∀ w ∈ feasibleSet p G, F v - ε * ‖w - v‖ ≤ F w)
    (h : V)
    (h13 : ∀ i : Fin m, i.val < p → fderiv ℝ (G i) v h = 0)
    (h14 : ∀ i : Fin m, p ≤ i.val → G i v = 0 → 0 ≤ fderiv ℝ (G i) v h) :
    -ε * ‖h‖ ≤ fderiv ℝ F v h := by sorry

end EkelandVP.Constraints
