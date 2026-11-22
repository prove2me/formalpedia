-- Prove2me | Theorems.Thm_CoeffFieldBounds
-- name    : CoeffFieldBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:21:20.703842+00:00
-- url     : https://prove2.me/theorems/f01c9dec-4d47-430d-9379-97435d0faeee
-- title:
--   Coeff Field Bounds: Coeff Field Bounds
-- statement:
--   The composition estimate for Holder classes: if `Phi` is smooth with derivatives of order
--   up to `j+1` bounded on a convex open set `V`, and `H` maps a convex open set `U` of bounded
--   diameter into `V` with derivatives of order up to `j` bounded and with `D^j H` Holder of
--   exponent `kappa`, then `Phi ∘ H` has derivatives of order up to `j` bounded and `D^j (Phi ∘ H)`
--   is Holder of exponent `kappa`, with a single constant `M` depending only on
--   `j, kappa, C, D, d` — produced BEFORE `U`, `V`, `Phi` and `H`, which is the uniformity the
--   application needs.
--
--   WHY THIS NODE EXISTS.  The Schauder bootstrap of `Noncritical` needs the coefficient field
--   `A x = D_xi A_p(Dv x)` to be `C^{j,kappa}`, i.e. BOTH sup bounds on `D^i A` for `i ≤ j` AND a
--   Holder estimate for `D^j A`.  `norm_iteratedFDeriv_comp_le` supplies the sup half only: it
--   bounds a norm at a point, whereas a Holder seminorm is a two-point difference.  Deriving the
--   Holder half from a sup bound on `D^(j+1) A` through the mean value inequality costs one
--   derivative of `v`, while each Schauder round gains exactly one, so that route makes the
--   bootstrap stall; this node supplies the Holder half directly and at no cost in order.
--
--   The proof uses only FIRST-order rules — the chain rule `D(Phi ∘ H) = (D Phi ∘ H) ∘ D H` and the
--   product rule for a continuous bilinear pairing — iterated by induction on the order, and never
--   expands `D^j (Phi ∘ H)` structurally, so it respects the standing prohibition on a Faa di Bruno
--   development.
--
--   The target `W` is an arbitrary normed real vector space because the induction applies the
--   statement to `D Phi`, whose values are continuous linear maps; the consumer takes
--   `W = Plane →L[ℝ] Plane`, `Phi = D_xi A_p` and `H = Dv`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CoeffFieldBounds.lean#L30-L219
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CoeffFieldBounds.lean#L30-L219

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_BilinearPairingBounds
import Definitions.Def_PHigherOrder_JetHolderDescent
import Definitions.Def_PHigherOrder_IteratedFDerivShiftTwoPoint
import Definitions.Def_PHigherOrder_CoeffFieldBounds
import Theorems.Thm_BilinearPairingBounds
import Theorems.Thm_IteratedFDerivShiftTwoPoint
import Theorems.Thm_JetHolderDescent

set_option autoImplicit false

theorem CoeffFieldBounds (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W]
    (j : ℕ) (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (C D d : ℝ) (hC : 0 < C) (hD : 0 < D) (hd : 0 < d) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (U V : Set Plane) (Φ : Plane → W) (H : Plane → Plane),
        IsOpen U → Convex ℝ U → (∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ d) →
        IsOpen V → Convex ℝ V → (∀ x ∈ U, H x ∈ V) →
        ContDiffOn ℝ (⊤ : ℕ∞) Φ V →
        (∀ i ≤ j + 1, ∀ ξ ∈ V, ‖iteratedFDeriv ℝ i Φ ξ‖ ≤ C) →
        ContDiffOn ℝ (⊤ : ℕ∞) H U →
        (∀ i ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ i H x‖ ≤ D) →
        (∀ x ∈ U, ∀ y ∈ U,
            ‖iteratedFDeriv ℝ j H x - iteratedFDeriv ℝ j H y‖ ≤ D * ‖x - y‖ ^ κ) →
        (∀ i ≤ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (Φ ∘ H) x‖ ≤ M)
          ∧ (∀ x ∈ U, ∀ y ∈ U,
              ‖iteratedFDeriv ℝ j (Φ ∘ H) x - iteratedFDeriv ℝ j (Φ ∘ H) y‖
                ≤ M * ‖x - y‖ ^ κ) := by sorry
