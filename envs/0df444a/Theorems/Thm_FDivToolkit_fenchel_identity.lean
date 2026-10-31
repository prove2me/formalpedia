-- Prove2me | Theorems.Thm_FDivToolkit_fenchel_identity
-- name    : FDivToolkit.fenchel_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:57.536148+00:00
-- url     : https://prove2.me/theorems/c3d35d42-5161-4fb8-adb9-6dc6e0bd6ed1
-- title:
--   Proof of Proposition 1, p.32 — the Fenchel identity
-- statement:
--   Let $H$ be a generating function and $\nu$ a reference model with density $f$ satisfying (5). Let $(\alpha_1,\alpha_2)\in\mathbb R\times(0,\infty)$ be such that $g^{wc}$ of (6) integrates to $1$. Then
--   $$
--   D_F(\eta^{wc}\,|\,\nu)=\alpha_1+\alpha_2\int_{\mathcal S}x\,g^{wc}(x)\,dx-K(\alpha_1,\alpha_2).
--   $$
--
--   It links the multiplier condition (28) to the divergence constraint, so that the worst-case parameters are characterized by $\int g^{wc}=1$ and $D_F(\eta^{wc}\,|\,\nu)=\kappa$.
--
--   Differences from the source:
--   - generalization: κ = α₁^wc + α₂^wc ∫ x g^wc dx − K(α₁^wc, α₂^wc) = … = D_F(η^wc|ν), for the solution of (28) → the equality of the last member with the second, for every (α₁, α₂) with α₂ > 0 and ∫ g^wc = 1; reason: the first equality is condition (28), quoted from Breuer and Csiszár; applied to a solution of (28), the Lean identity gives the display
--   - encoding: distributions ν, η on 𝓢 with densities f, g → functions f, g : ℝ → ℝ with IsRefModel f and IsDensity g, the distributions being densityMeasure f and densityMeasure g, and integrals over 𝓢 written over ℝ where f or g vanishes off 𝓢; reason: the paper uses its distributions only through their densities; measurability is the standing convention of the field, and f = 0 off 𝓢 by footnote 2
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), proof of Proposition 1, p.32

import Definitions.Def_FDivToolkit_IsRefModel
import Definitions.Def_FDivToolkit_Cond5
import Definitions.Def_FDivToolkit_gwc
import Definitions.Def_FDivToolkit_Fstar

namespace FDivToolkit

/-- The identity closing the proof of Proposition 1, Kruse, Schneider & Schweizer, SSRN 3680475
(Aug 25, 2020), p.32: under (5), for every `(α₁, α₂) ∈ ℝ × (0, ∞)` for which `g^wc` integrates to `1`,
`α₁ + α₂ ∫_𝓢 x g^wc(x) dx − K(α₁, α₂) = D_F(η^wc|ν)`.

**Formalization Note.** The paper writes `κ` for the left-hand side, by (28); that first equality is
the multiplier condition taken from Breuer and Csiszár (2016) and is not part of this statement. The
left-hand side is nonnegative, so `ENNReal.ofReal` loses nothing. Integrability of `x g^wc(x)` and of
the integrand of `K` follows from (5) and is not assumed. -/
theorem fenchel_identity {H f : ℝ → ℝ} (hH : IsAdmissibleH H) (hf : IsRefModel f) (h5 : Cond5 H f)
    (α : ℝ × ℝ) (hα : 0 < α.2) (h1 : ∫ x, gwc H f α x = 1) :
    fDiv (Fbar H) f (gwc H f α) =
      ENNReal.ofReal (α.1 + α.2 * (∫ x, x * gwc H f α x) - K H f α) := by sorry

end FDivToolkit
