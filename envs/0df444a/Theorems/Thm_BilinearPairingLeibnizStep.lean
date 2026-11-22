-- Prove2me | Theorems.Thm_BilinearPairingLeibnizStep
-- name    : BilinearPairingLeibnizStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:15:24.535143+00:00
-- url     : https://prove2.me/theorems/30da0f74-ec4f-40c2-a97e-4813243643b7
-- title:
--   Bilinear Pairing Leibniz Step: Bilinear Pairing Leibniz Step
-- statement:
--   THE LEIBNIZ INDUCTION STEP for the bilinear-pairing Holder bound: the order-`n` bound
--   PROMOTES to order `n + 1`.
--
--   The hypothesis `ih` is the order-`n` statement in the uniform form the induction carries it:
--   for EVERY positive constant `L` there is a constant `q > 0` -- produced before the spaces, the
--   pairing and the data -- such that a pairing `B` with the pointwise bound `‖B a b‖ ≤ ‖a‖ * ‖b‖`
--   sends any pair `F, G` whose jets to order `n` are bounded by `L` and whose order-`n` jets are
--   `κ`-Holder with constant `L`, on an open convex `U` of diameter at most `d`, to a map
--   `y ↦ B (F y) (G y)` with the same two bounds at `q`.  The conclusion is that same statement at
--   order `n + 1`, with a NEW constant.
--
--   Quantifying `ih` over every `L` rather than at one fixed constant is what makes the step
--   self-contained: the proof differentiates, which costs one order, and pays for it by invoking
--   `ih` at the LARGER constant `L * θ`, where `θ ≥ 1` is the descent factor this node obtains for
--   itself from `JetHolderDescent`.  So no witness has to be threaded in from the caller, and the
--   step's only parameters are `κ`, `d`, their two admissibility hypotheses -- which exist solely to
--   feed `JetHolderDescent` -- and the order `n`.
--
--   The mechanism is the product rule: `D(B(F,G)) = B₁(G, DF) + B₂(F, DG)` for the two induced
--   pairings `B₁`, `B₂`, each of which again satisfies a POINTWISE bound.  That is the whole reason
--   the hypothesis on `B` is pointwise rather than `‖B‖ ≤ 1`: at this instantiation the arguments
--   are themselves spaces of continuous linear maps, where Mathlib's operator norm needs a
--   nontriviality side condition the ambient typeclasses cannot supply, so `‖B₁‖ ≤ 1` is not even
--   well-formed.  Applying `ih` to each summand and recombining through the order shift gives both
--   halves at order `n + 1`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/BilinearPairingLeibnizStep.lean#L31-L200
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/BilinearPairingLeibnizStep.lean#L31-L200

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_JetSumBounds
import Definitions.Def_PHigherOrder_JetHolderDescent
import Definitions.Def_PHigherOrder_IteratedFDerivShiftTwoPoint
import Definitions.Def_PHigherOrder_BilinearPairingLeibnizStep
import Theorems.Thm_IteratedFDerivShiftTwoPoint
import Theorems.Thm_JetHolderDescent
import Theorems.Thm_JetSumBounds

set_option autoImplicit false

theorem BilinearPairingLeibnizStep (κ d : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (n : ℕ)
    (ih : ∀ L : ℝ, 0 < L → ∃ q : ℝ, 0 < q ∧
          ∀ (Z₁ Z₂ Z₃ : Type) [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]
            [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂]
            [NormedAddCommGroup Z₃] [NormedSpace ℝ Z₃]
            (B : Z₁ →L[ℝ] Z₂ →L[ℝ] Z₃), (∀ (a : Z₁) (b : Z₂), ‖B a b‖ ≤ ‖a‖ * ‖b‖) →
          ∀ U : Set Plane, IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
          ∀ (F : Plane → Z₁) (G : Plane → Z₂),
            ContDiffOn ℝ (⊤ : ℕ∞) F U →
            (∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ L) →
            (∀ x ∈ U, ∀ y ∈ U,
              ‖iteratedFDeriv ℝ n F x - iteratedFDeriv ℝ n F y‖ ≤ L * ‖x - y‖ ^ κ) →
            ContDiffOn ℝ (⊤ : ℕ∞) G U →
            (∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i G x‖ ≤ L) →
            (∀ x ∈ U, ∀ y ∈ U,
              ‖iteratedFDeriv ℝ n G x - iteratedFDeriv ℝ n G y‖ ≤ L * ‖x - y‖ ^ κ) →
            ((∀ i ≤ n, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (fun y => B (F y) (G y)) x‖ ≤ q) ∧
              ∀ x ∈ U, ∀ y ∈ U, ‖iteratedFDeriv ℝ n (fun y => B (F y) (G y)) x
                - iteratedFDeriv ℝ n (fun y => B (F y) (G y)) y‖ ≤ q * ‖x - y‖ ^ κ)) :
    ∀ L : ℝ, 0 < L → ∃ q : ℝ, 0 < q ∧
      ∀ (Z₁ Z₂ Z₃ : Type) [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]
        [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂]
        [NormedAddCommGroup Z₃] [NormedSpace ℝ Z₃]
        (B : Z₁ →L[ℝ] Z₂ →L[ℝ] Z₃), (∀ (a : Z₁) (b : Z₂), ‖B a b‖ ≤ ‖a‖ * ‖b‖) →
      ∀ U : Set Plane, IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
      ∀ (F : Plane → Z₁) (G : Plane → Z₂),
        ContDiffOn ℝ (⊤ : ℕ∞) F U →
        (∀ i ≤ (n + 1), ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ L) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ (n + 1) F x - iteratedFDeriv ℝ (n + 1) F y‖ ≤ L * ‖x - y‖ ^ κ) →
        ContDiffOn ℝ (⊤ : ℕ∞) G U →
        (∀ i ≤ (n + 1), ∀ x ∈ U, ‖iteratedFDeriv ℝ i G x‖ ≤ L) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ (n + 1) G x - iteratedFDeriv ℝ (n + 1) G y‖ ≤ L * ‖x - y‖ ^ κ) →
        ((∀ i ≤ (n + 1), ∀ x ∈ U, ‖iteratedFDeriv ℝ i (fun y => B (F y) (G y)) x‖ ≤ q) ∧
          ∀ x ∈ U, ∀ y ∈ U, ‖iteratedFDeriv ℝ (n + 1) (fun y => B (F y) (G y)) x
            - iteratedFDeriv ℝ (n + 1) (fun y => B (F y) (G y)) y‖ ≤ q * ‖x - y‖ ^ κ) := by sorry
