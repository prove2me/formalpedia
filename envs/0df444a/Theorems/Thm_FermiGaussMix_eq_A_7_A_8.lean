-- Prove2me | Theorems.Thm_FermiGaussMix_eq_A_7_A_8
-- name    : FermiGaussMix.eq_A_7_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:39.702035+00:00
-- url     : https://prove2.me/theorems/7b44f72d-4cee-41e8-b308-26b7826d03ea
-- title:
--   Eqs. (A.7)–(A.8) — monomials are orthonormal and $|o_R|\le\|O\|$
-- statement:
--   The Majorana monomials are orthonormal for the normalized trace: for even $R,T$,
--   $$
--   2^{-n}\operatorname{Tr}(P_RP_T)=\delta_{R,T}.
--   $$
--   Consequently an expansion $O=\sum_Ro_RP_R$ over even sets has $o_R=2^{-n}\operatorname{Tr}(P_RO)$. Moreover, for every operator $O$ and every even $R$,
--   $$
--   \bigl|2^{-n}\operatorname{Tr}(P_RO)\bigr|\le\|O\|,
--   $$
--   where $\|\cdot\|$ is the operator norm. This turns the norm bounds of the local terms into coefficient bounds.
--
--   Differences from the source:
--   - generalization: |o_R| ≤ ∥O∥ for O = Σ_R o_R P_R → the bound for every operator O and every even R; reason: an operator with an expansion in even monomials is a special case
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, eqs. (A.7)–(A.8), p. 9

import Mathlib
import Definitions.Def_FermiGaussMix_coeff

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Eqs. (A.7)–(A.8), p.9** (Han, Zhao, Liu, arXiv:2609.35159v1). The monomials are orthonormal for the
normalized trace; an expansion `O = Σ_R o_R P_R` has `o_R = 2^{-n} Tr(P_R O)`; and `|2^{-n} Tr(P_R O)| ≤ ‖O‖`.

**Formalization Note** The norm is the operator norm. The bound is stated for every operator `O` and even `R`,
which contains the printed case of an expansion in even monomials. -/
theorem eq_A_7_A_8 {n : ℕ} :
    (∀ R T : Finset (Fin (2 * n)), Even R.card → Even T.card →
      (2 : ℂ)⁻¹ ^ n * (P n R * P n T).trace = if R = T then 1 else 0) ∧
    (∀ (o : Finset (Fin (2 * n)) → ℂ) (R : Finset (Fin (2 * n))), Even R.card →
      coeff (∑ T ∈ evenSets n, o T • P n T) R = o R) ∧
    (∀ (O : Op n) (R : Finset (Fin (2 * n))), Even R.card → ‖coeff O R‖ ≤ ‖O‖) := by sorry

end FermiGaussMix
