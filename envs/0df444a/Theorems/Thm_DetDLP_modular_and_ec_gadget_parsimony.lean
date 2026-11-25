-- Prove2me | Theorems.Thm_DetDLP_modular_and_ec_gadget_parsimony
-- name    : DetDLP.modular_and_ec_gadget_parsimony
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T12:26:59.254005+00:00
-- url     : https://prove2.me/theorems/14aa1032-2003-4f41-87d4-a528203bdc3c
-- title:
--   Parsimony of Modular Arithmetic, Zero-Test, and Short-Weierstrass Elliptic-Curve Addition Gadgets
-- statement:
--   Proves the algebraic parsimony (existence and uniqueness of intermediate wire values) of the modular arithmetic, prime-field zero-test, and elliptic-curve addition gadgets (Lemmas 2.4 & 2.5):
--
--   1. **Modular addition wrap bit:** $x+y=s_{\mathrm{sum}} \wedge z+\gamma q=s_{\mathrm{sum}}$ uniquely determines $\gamma = \mathbf{1}[x+y\ge q]$ and $z = (x+y)\bmod q$;
--   2. **Euclidean modular multiplication:** $x y = u_1 \wedge \theta q = u_2 \wedge u_2 + z = u_1$ ($z<q$) uniquely determines $\theta = \lfloor xy/q\rfloor < q$ and $z = (xy)\bmod q$;
--   3. **Prime-field zero indicator:** $\zeta u = 0 \wedge \zeta w_{\mathrm{inv}} = 0 \wedge (1-\zeta)(u w_{\mathrm{inv}}) = 1-\zeta$ over $\mathbb{F}_p$ has the unique solution $(\zeta, w_{\mathrm{inv}}) = (\mathbf{1}[u=0], u^{-1})$;
--   4. **Short-Weierstrass 5-branch partition of unity & gated slope uniqueness:** $\sigma_1,\dots,\sigma_5 \in \{0,1\}$ sum to $1$, and the gated slope equations $\sigma_4 r_4 = 0, \sigma_5 r_5 = 0, (1-\sigma_4-\sigma_5)\lambda_{\mathrm{sl}}=0$ uniquely determine $\lambda_{\mathrm{sl}} \in \mathbb{F}_p$ in all five branches.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proofs of Lemmas 2.4 and 2.5 (pp. 9–10)

import Mathlib

set_option autoImplicit false

namespace DetDLP

/-- Algebraic parsimony of the modular arithmetic, zero-test, and short-Weierstrass elliptic-curve
addition gadgets (Section 2.3, Lemmas 2.4 & 2.5, pp. 9–10):
(1) Modular addition wrap-bit and sum-word uniqueness;
(2) Euclidean modular multiplication quotient and product-word uniqueness;
(3) Prime-field zero-indicator 3-equation gated inverse parsimony;
(4) Short-Weierstrass 5-branch partition of unity and gated chord/tangent slope uniqueness. -/
theorem modular_and_ec_gadget_parsimony :
    (∀ (q x y z : ℕ) (γ : Bool) (ssum : ℕ),
       x < q → y < q → z < q →
       ((x + y = ssum ∧ z + (if γ then 1 else 0) * q = ssum) ↔
         (z = (x + y) % q ∧ γ = decide (q ≤ x + y) ∧ ssum = x + y))) ∧
    (∀ (q x y z θ u₁ u₂ : ℕ),
       x < q → y < q → z < q →
       ((x * y = u₁ ∧ θ * q = u₂ ∧ u₂ + z = u₁) ↔
         (z = (x * y) % q ∧ θ = (x * y) / q ∧ θ < q ∧ u₁ = x * y ∧ u₂ = ((x * y) / q) * q))) ∧
    (∀ (p : ℕ) [Fact p.Prime] (u : ZMod p) (ζ : Bool) (winv : ZMod p),
       (((if ζ then (1 : ZMod p) else 0) * u = 0 ∧
         (if ζ then (1 : ZMod p) else 0) * winv = 0 ∧
         (1 - (if ζ then (1 : ZMod p) else 0)) * (u * winv) =
           1 - (if ζ then (1 : ZMod p) else 0)) ↔
        (ζ = decide (u = 0) ∧ winv = u⁻¹))) ∧
    ((∀ (ι₁ ι₂ ζx ζy : Bool),
        let b : Bool → ℤ := fun x => if x then 1 else 0
        let σ₁ := b ι₁
        let σ₂ := (1 - b ι₁) * b ι₂
        let σ₃ := (1 - b ι₁) * (1 - b ι₂) * b ζx * b ζy
        let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
        let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
        (σ₁ = 0 ∨ σ₁ = 1) ∧ (σ₂ = 0 ∨ σ₂ = 1) ∧ (σ₃ = 0 ∨ σ₃ = 1) ∧
        (σ₄ = 0 ∨ σ₄ = 1) ∧ (σ₅ = 0 ∨ σ₅ = 1) ∧
        σ₁ + σ₂ + σ₃ + σ₄ + σ₅ = 1) ∧
     (∀ (p : ℕ) [Fact p.Prime], 2 < p →
        ∀ (aE bE x₁ y₁ x₂ y₂ lsl : ZMod p) (ι₁ ι₂ : Bool),
          y₁ ^ 2 = x₁ ^ 3 + aE * x₁ + bE →
          y₂ ^ 2 = x₂ ^ 3 + aE * x₂ + bE →
          let ζx := decide (x₂ - x₁ = 0)
          let ζy := decide (y₁ + y₂ = 0)
          let b : Bool → ZMod p := fun x => if x then 1 else 0
          let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
          let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
          ((σ₄ * ((x₂ - x₁) * lsl - (y₂ - y₁)) = 0 ∧
            σ₅ * (2 * y₁ * lsl - (3 * x₁ ^ 2 + aE)) = 0 ∧
            (1 - σ₄ - σ₅) * lsl = 0) ↔
           lsl =
             if (!ι₁ && !ι₂ && !ζx) then (y₂ - y₁) * (x₂ - x₁)⁻¹
             else if (!ι₁ && !ι₂ && ζx && !ζy) then (3 * x₁ ^ 2 + aE) * (2 * y₁)⁻¹
             else 0))) := by sorry

end DetDLP
