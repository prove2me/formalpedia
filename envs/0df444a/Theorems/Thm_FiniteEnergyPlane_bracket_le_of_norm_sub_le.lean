-- Prove2me | Theorems.Thm_FiniteEnergyPlane_bracket_le_of_norm_sub_le
-- name    : FiniteEnergyPlane.bracket_le_of_norm_sub_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-23T16:06:24.238077+00:00
-- url     : https://prove2.me/theorems/68dcdc45-bee7-42f4-a57d-e43dd116a9ba
-- title:
--   Bracket and area-density bounds for an operator close to a complex structure, in the $J_0$-invariant inner product
-- statement:
--   Let $F$ be a real inner product space and $J_0:F\to F$ a bounded linear map with $J_0^2=-\mathrm{id}$ and $\|J_0\|\le\beta$. Put
--   $$g(v,v')=\langle v,v'\rangle+\langle J_0v,J_0v'\rangle ,\qquad \gamma=1+\beta^2 .$$
--   Let $A:F\to F$ be bounded linear with $\|A-J_0\|\le\varepsilon$, and let $w,x\in F$. Then
--   $$g(w,x)\,g(J_0w,Ax)-g(w,Ax)\,g(J_0w,x)\ \le\ g(w,w)\,g(x,x)\,\bigl(1+2\gamma^2\beta\varepsilon\bigr)$$
--   and
--   $$g(x,x)\,\bigl(1-\gamma\beta\varepsilon\bigr)\ \le\ g(J_0x,Ax).$$
--
--   For $A=J_0$ these say that the bracket is at most $g(w,w)g(x,x)$ and that $g(J_0x,J_0x)=g(x,x)$. In the application $A=J(u(z))$, $x=\partial_su$, $Ax=\partial_tu$ and $w=u(z)-q$, so the two quantities are the angular term and the area density $\omega_q(\partial_su,\partial_tu)$ of a pseudoholomorphic map near a point $q$ with $J(q)=J_0$.
--
--   **Formalization Note** The form $g$ is written out with `inner ℝ`; the operators are `F →L[ℝ] F`, and $J_0^2=-\mathrm{id}$ is `J₀.comp J₀ = -ContinuousLinearMap.id ℝ F`.
-- source:
--   Used for the monotonicity lemma, A. Zinger, Notes on J-holomorphic maps, arXiv:1706.00331, Proposition 3.12; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, p. 152

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

namespace FiniteEnergyPlane

/-- Let `J₀` be a complex structure (`J₀² = -1`, `‖J₀‖ ≤ β`) on a real inner product space and
`g(v, v') = ⟪v, v'⟫ + ⟪J₀ v, J₀ v'⟫`. For an operator `A` with `‖A - J₀‖ ≤ ε` and vectors `w, x`,
with `γ = 1 + β²`:
`g(w, x) g(J₀ w, A x) - g(w, A x) g(J₀ w, x) ≤ g(w, w) g(x, x) (1 + 2 γ² β ε)` and
`g(x, x) (1 - γ β ε) ≤ g(J₀ x, A x)`. -/
theorem bracket_le_of_norm_sub_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J₀ A : F →L[ℝ] F) (hJ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ F) {β ε : ℝ}
    (hβ : ‖J₀‖ ≤ β) (hε : ‖A - J₀‖ ≤ ε) (w x : F) :
    (inner ℝ w x + inner ℝ (J₀ w) (J₀ x)) *
        (inner ℝ (J₀ w) (A x) + inner ℝ (J₀ (J₀ w)) (J₀ (A x))) -
      (inner ℝ w (A x) + inner ℝ (J₀ w) (J₀ (A x))) *
        (inner ℝ (J₀ w) x + inner ℝ (J₀ (J₀ w)) (J₀ x)) ≤
      (inner ℝ w w + inner ℝ (J₀ w) (J₀ w)) * (inner ℝ x x + inner ℝ (J₀ x) (J₀ x)) *
        (1 + 2 * (1 + β ^ 2) ^ 2 * β * ε) ∧
    (inner ℝ x x + inner ℝ (J₀ x) (J₀ x)) * (1 - (1 + β ^ 2) * β * ε) ≤
      inner ℝ (J₀ x) (A x) + inner ℝ (J₀ (J₀ x)) (J₀ (A x)) := by
  sorry

end FiniteEnergyPlane
