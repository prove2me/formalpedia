-- Prove2me | Theorems.Thm_BraneBrauer_Orthogonal_eq_7_13_wick
-- name    : BraneBrauer.Orthogonal.eq_7_13_wick
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:32.055669+00:00
-- url     : https://prove2.me/theorems/e03c2c67-621a-4781-921d-1244c6ce2a14
-- title:
--   (7.13), second line — two-matrix Wick sum
-- statement:
--   Let $X_1,X_2$ be arbitrary operators on $V^{\otimes m}\otimes\bar V^{\otimes n}$. The Gaussian inner product of their polynomial states is
--   $$
--   \langle X_2,X_1\rangle
--   =\sum_{\sigma\in S_m}\sum_{\tau\in S_n}
--   \operatorname{tr}_{m,n}\!\left[
--   P_{\sigma,\tau}X_2^\dagger P_{\sigma^{-1},\tau^{-1}}X_1
--   \right],
--   $$
--   where $P_{\sigma,\tau}$ permutes the tensor legs.
--
--   This converts all Wick contractions into the tensor-space trace expression used in (7.13).
--
--   **Formalization Note** The paper inserts $X_s=\Sigma(Q_s)$; the identity itself applies to every operator and needs no Brauer or symmetry hypothesis.
-- source:
--   Kimura & Ramgoolam, Branes, Anti-Branes and Brauer Algebras in Gauge-Gravity duality, arXiv:0709.2158v2, p. 29, (7.13), second line

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_Setting

noncomputable section
open Matrix
open scoped BigOperators

namespace BraneBrauer.Orthogonal

/-- (7.13), second line, p. 29: the two-matrix Gaussian inner product
is the sum over all Wick permutations in the two tensor factors. -/
theorem eq_7_13_wick {N m n : ℕ} (X₂ X₁ : Op N m n) :
    innerProd N m n X₂ X₁ =
      ∑ σ : Equiv.Perm (Fin m),
        ∑ τ : Equiv.Perm (Fin n),
          (permOp N m n σ τ * X₂ᴴ *
            permOp N m n σ⁻¹ τ⁻¹ * X₁).trace := by sorry

end BraneBrauer.Orthogonal
