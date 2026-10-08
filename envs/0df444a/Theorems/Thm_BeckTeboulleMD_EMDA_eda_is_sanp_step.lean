-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_eda_is_sanp_step
-- name    : BeckTeboulleMD.EMDA.eda_is_sanp_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T05:54:25.515737+00:00
-- url     : https://prove2.me/theorems/f12e887c-e56b-44af-b6e3-3ada7d4c1ef3
-- title:
--   EDA, p. 174 — the EDA update is the SANP step (3.11) with ψ = ψ_e on X = Δ and stays in int Δ
-- statement:
--   Let $y \in \operatorname{int}\Delta$ (all $y_j > 0$, $\sum_j y_j = 1$), $z \in \mathbb R^n$ and $t > 0$, and define
--   $$w_j = \frac{y_j\, e^{-t z_j}}{\sum_{i=1}^n y_i\, e^{-t z_i}}, \qquad j = 1, \dots, n.$$
--   Then $w \in \operatorname{int}\Delta$, and $w$ minimises the SANP objective over the simplex:
--   $$\langle w, z\rangle + \frac1t B_{\psi_e}(w, y) \le \langle u, z\rangle + \frac1t B_{\psi_e}(u, y) \qquad \text{for all } u \in \Delta.$$
--
--   With $z = f'(x^k)$ and $y = x^k$, this says that the entropic descent algorithm (EDA) is exactly SANP (3.11) with $X = \Delta$ and $\psi = \psi_e$, and that its iterates remain in the relative interior of $\Delta$, so that Theorems 4.1 and 4.2 apply to it.
--
--   **Formalization Note** The page derives the EDA by "using the entropy function $\psi_e$ in (3.12)", that is, in SANP with a $\psi$ satisfying (3.12); this item states the resulting identification for one step. $\langle u, z\rangle = \sum_j u_j z_j$, and $B_{\psi_e}(u, y)$ uses the derivative of $\psi_e$ at $y$, which exists because $y$ has positive entries.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 174, the entropic descent algorithm (EDA) and the sentence preceding it

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- The EDA is SANP with `ψ_e` on `Δ`, p. 174: for `y` in the relative interior of `Δ`, a vector `z`
(the subgradient `f′(y)`) and `t > 0`, the point `w_j = y_j e^{−t z_j} / ∑_i y_i e^{−t z_i}` lies in
the relative interior of `Δ` and minimises `u ↦ ⟨u, z⟩ + (1/t) B_{ψ_e}(u, y)` over `Δ`. -/
theorem eda_is_sanp_step {n : ℕ} (y : Fin n → ℝ) (hy : y ∈ relIntSimplex n)
    (z : Fin n → ℝ) (t : ℝ) (ht : 0 < t) :
    (fun j => y j * Real.exp (-(t * z j)) / ∑ i, y i * Real.exp (-(t * z i))) ∈ relIntSimplex n ∧
    ∀ u ∈ stdSimplex ℝ (Fin n),
      ∑ j, (y j * Real.exp (-(t * z j)) / ∑ i, y i * Real.exp (-(t * z i))) * z j
          + (1 / t) * bregman (entropy (n := n))
              (fun j => y j * Real.exp (-(t * z j)) / ∑ i, y i * Real.exp (-(t * z i))) y
        ≤ ∑ j, u j * z j + (1 / t) * bregman (entropy (n := n)) u y := by sorry

end BeckTeboulleMD.EMDA
