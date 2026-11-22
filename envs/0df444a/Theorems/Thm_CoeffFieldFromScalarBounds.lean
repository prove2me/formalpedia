-- Prove2me | Theorems.Thm_CoeffFieldFromScalarBounds
-- name    : CoeffFieldFromScalarBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:23:57.037804+00:00
-- url     : https://prove2.me/theorems/039329d2-e531-4bba-a15f-a9c126371d61
-- title:
--   Coeff Field From Scalar Bounds: Coeff Field From Scalar Bounds
-- statement:
--   The coefficient field `Phi . Dv` is `C^{j,kappa}` as soon as the SCALAR function `v` carries
--   `C^{j+1,kappa}` bounds.
--
--   `CoeffFieldBounds` takes its hypotheses on the `Plane`-valued map `H` it composes with, but the
--   Schauder bootstrap of the paper's lem:noncritical carries its inductive hypothesis on the scalar
--   solution `v`, and applies the composition estimate with `H := Dv`, the CLASSICAL GRADIENT FIELD.
--   This node performs that conversion and then the composition estimate, so the bootstrap can quote
--   one node for the whole of its step "the coefficient field is `C^{i,kappa}`".
--
--   The conversion is at NO loss of constant: `D^{n}(Dv)(x)` and `D^{n+1}v(x)` differ by a fixed
--   linear isometry, namely the Riesz map post-composed into the `n`-linear maps and then the
--   order-shift isometry, so their norms agree and so do the norms of their two-point differences.
--   That the Riesz map must be inserted at all is the whole content of the conversion: the order-shift
--   proposition differentiates the Frechet derivative `Df : Plane -> L(Plane, R)`, which takes values
--   in the dual of the plane, whereas the classical gradient field `Dv : Plane -> Plane` takes values
--   in the plane itself, and this development keeps the two apart.
--
--   As in `CoeffFieldBounds`, the constant `M` is quantified BEFORE `U`, `V`, `Phi` and `v`, which is
--   what lets the bootstrap fix all of its constants before any solution is given.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CoeffFieldFromScalarBounds.lean#L23-L54
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CoeffFieldFromScalarBounds.lean#L23-L54

import Definitions.Def_PHigherOrder_CoeffFieldBounds
import Definitions.Def_PHigherOrder_GradientFieldOrderShift
import Definitions.Def_PHigherOrder_CoeffFieldFromScalarBounds
import Theorems.Thm_CoeffFieldBounds
import Theorems.Thm_GradientFieldOrderShift

set_option autoImplicit false

theorem CoeffFieldFromScalarBounds (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    (j : ℕ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (C D d : ℝ) (hC : 0 < C) (hD : 0 < D) (hd : 0 < d) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (U V : Set Plane) (Φ : Plane → W) (v : Plane → ℝ),
        IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
        IsOpen V → Convex ℝ V → (∀ x ∈ U, gradient v x ∈ V) →
        ContDiffOn ℝ (⊤ : ℕ∞) Φ V →
        (∀ i ≤ j + 1, ∀ ξ ∈ V, ‖iteratedFDeriv ℝ i Φ ξ‖ ≤ C) →
        ContDiffOn ℝ (⊤ : ℕ∞) v U →
        (∀ i ≤ j + 1, ∀ x ∈ U, ‖iteratedFDeriv ℝ i v x‖ ≤ D) →
        (∀ x ∈ U, ∀ y ∈ U,
            ‖iteratedFDeriv ℝ (j + 1) v x - iteratedFDeriv ℝ (j + 1) v y‖ ≤ D * ‖x - y‖ ^ κ) →
        (∀ i ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (Φ ∘ gradient v) x‖ ≤ M)
          ∧ (∀ x ∈ U, ∀ y ∈ U,
              ‖iteratedFDeriv ℝ j (Φ ∘ gradient v) x - iteratedFDeriv ℝ j (Φ ∘ gradient v) y‖
                ≤ M * ‖x - y‖ ^ κ) := by sorry
