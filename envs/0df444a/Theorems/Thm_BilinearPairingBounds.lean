-- Prove2me | Theorems.Thm_BilinearPairingBounds
-- name    : BilinearPairingBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:18:36.461737+00:00
-- url     : https://prove2.me/theorems/bb8fa293-eb9f-4e07-aa8d-323cacd2d1fc
-- title:
--   Bilinear Pairing Bounds: Bilinear Pairing Bounds
-- statement:
--   A continuous bilinear pairing preserves `C^{m,kappa}` bounds.  If `F` and `G` are smooth on
--   an open convex `U` of diameter at most `d`, with derivatives of order up to `m` bounded by `K`
--   and with `D^m F`, `D^m G` both `kappa`-Holder with constant `K`, then `y ↦ B (F y) (G y)` obeys
--   the same two bounds with a single constant `q` depending only on `m, K, kappa, d` — produced
--   BEFORE the spaces, the pairing and the data, which is the uniformity the induction needs.
--
--   WHY THE HYPOTHESIS ON `B` IS POINTWISE AND NOT `‖B‖ ≤ 1`.  The induction applies this statement
--   to pairings whose arguments are themselves spaces of continuous linear maps, i.e. at
--   `Z₁ := Z₂`, `Z₂ := Plane →L[ℝ] Z₁`, `Z₃ := Plane →L[ℝ] Z₃`.  At that instantiation the type
--   `Z₂ →L[ℝ] (Plane →L[ℝ] Z₁) →L[ℝ] (Plane →L[ℝ] Z₃)` carries NO `Norm` instance, because
--   Mathlib's norm on a space of continuous linear maps needs a nontriviality side condition on the
--   domain that `[NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]` cannot supply — `Z₁` is allowed to be
--   the zero space.  So `‖B‖ ≤ 1` is not even well-formed there.  The pointwise bound
--   `‖B a b‖ ≤ ‖a‖ * ‖b‖` mentions `Norm` only on the three spaces themselves, is well-formed at
--   every nesting depth, and is all the proof uses.
--
--   The target spaces are arbitrary normed real vector spaces precisely because the inductive step
--   applies the statement to derivatives, whose values are continuous linear maps.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/BilinearPairingBounds.lean#L22-L121
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/BilinearPairingBounds.lean#L22-L121

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_BilinearPairingLeibnizStep
import Definitions.Def_PHigherOrder_BilinearPairingBounds
import Theorems.Thm_BilinearPairingLeibnizStep

set_option autoImplicit false

theorem BilinearPairingBounds (κ d : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (_hd : 0 < d)
    (m : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ q : ℝ, 0 < q ∧
      ∀ (Z₁ Z₂ Z₃ : Type) [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]
        [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂]
        [NormedAddCommGroup Z₃] [NormedSpace ℝ Z₃]
        (B : Z₁ →L[ℝ] Z₂ →L[ℝ] Z₃), (∀ (a : Z₁) (b : Z₂), ‖B a b‖ ≤ ‖a‖ * ‖b‖) →
      ∀ U : Set Plane, IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
      ∀ (F : Plane → Z₁) (G : Plane → Z₂),
        ContDiffOn ℝ (⊤ : ℕ∞) F U →
        (∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ K) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ m F x - iteratedFDeriv ℝ m F y‖ ≤ K * ‖x - y‖ ^ κ) →
        ContDiffOn ℝ (⊤ : ℕ∞) G U →
        (∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i G x‖ ≤ K) →
        (∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ m G x - iteratedFDeriv ℝ m G y‖ ≤ K * ‖x - y‖ ^ κ) →
        ((∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (fun y => B (F y) (G y)) x‖ ≤ q) ∧
          ∀ x ∈ U, ∀ y ∈ U, ‖iteratedFDeriv ℝ m (fun y => B (F y) (G y)) x
            - iteratedFDeriv ℝ m (fun y => B (F y) (G y)) y‖ ≤ q * ‖x - y‖ ^ κ) := by sorry
