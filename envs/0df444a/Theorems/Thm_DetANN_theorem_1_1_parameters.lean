-- Prove2me | Theorems.Thm_DetANN_theorem_1_1_parameters
-- name    : DetANN.theorem_1_1_parameters
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:26:27.667263+00:00
-- url     : https://prove2.me/theorems/1b636d62-0ecc-47dd-aaad-f04c10eb46f8
-- title:
--   Proof of Theorem 1.1, p.19 — the parameters $\delta=\varepsilon/100$, $\tau=\varepsilon^2/10^6$, $\ell=\lceil\log_{1/\theta_0}(200/\varepsilon)\rceil$ give factor $\le1+\varepsilon$
-- statement:
--   Let $\varepsilon\in(0,1)$, $\theta_0=5\sqrt2/8$, and put
--
--   $$\delta=\frac{\varepsilon}{100},\qquad\tau=\frac{\varepsilon^2}{10^6},\qquad\ell=\big\lceil\log_{1/\theta_0}(200/\varepsilon)\big\rceil,\qquad\rho=\theta_0^{\ell},\qquad\alpha=1+\delta .$$
--
--   Then
--
--   1. $\ell\ge1$;
--   2. $\rho\le\varepsilon/200$;
--   3. $\rho^2/(1-\rho^2)\le\varepsilon^2/10^4$;
--   4. substituting the bound of item 3 and $\alpha=1+\delta$ into (27) gives an approximation factor at most $1+\varepsilon$:
--   $$\frac{\alpha+\sqrt{2\alpha^2\varepsilon^2/10^4+12\tau(1+\alpha)^2}}{\sqrt{1-\tau}}\le1+\varepsilon .$$
--
--   These are the parameter choices that turn the general bound (27) into the guarantee of Theorem 1.1.
--
--   Differences from the source:
--   - reading: θ₀ the constant of Lemma 7.1 → θ₀ = 5√2/8; reason: the proof of Lemma 7.1 (p.20) fixes θ₀ = 5√2/8, and the mission's graph milestone uses that value
--   - generalization: ℓ set by the formula (a positive integer, §7.1) → also concludes 1 ≤ ℓ; reason: an added true conclusion; dropping it gives the printed statement
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Proof of Theorem 1.1, §7.4, p.19 (PDF p.19); θ₀ from the proof of Lemma 7.1, p.20

import Mathlib
import Definitions.Def_DetANN_Multigraph

namespace DetANN

/-- **Proof of Theorem 1.1, the parameters** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §7.4, p.19).
For `ε ∈ (0, 1)` put `δ = ε/100`, `τ = ε²/10⁶`, `ℓ = ⌈log_{1/θ₀}(200/ε)⌉` with `θ₀ = 5√2/8`, `ρ = θ₀^ℓ` and
`α = 1 + δ`. Then `ℓ ≥ 1`, `ρ ≤ ε/200`, `ρ²/(1 − ρ²) ≤ ε²/10⁴`, and substituting the bound
`ρ²/(1 − ρ²) ≤ ε²/10⁴` and `α = 1 + δ` into (27) gives an approximation factor at most `1 + ε`:
`(α + √(2α² ε²/10⁴ + 12τ(1 + α)²))/√(1 − τ) ≤ 1 + ε`.

**Formalization Note.** `ℓ` is `Nat.ceil (Real.logb (1/θ₀) (200/ε))`. `θ₀ = 5√2/8` is the constant fixed
in the proof of Lemma 7.1 (p.20). The factor of (27) increases with `ρ²/(1 − ρ²)`, so the last clause
also bounds the factor at `ρ = θ₀^ℓ`. The clause `ℓ ≥ 1` records that `ℓ` is a positive integer, as
§7.1 requires. -/
theorem theorem_1_1_parameters (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 ≤ ⌈Real.logb (1 / theta0) (200 / ε)⌉₊ ∧
    theta0 ^ ⌈Real.logb (1 / theta0) (200 / ε)⌉₊ ≤ ε / 200 ∧
    (theta0 ^ ⌈Real.logb (1 / theta0) (200 / ε)⌉₊) ^ 2 /
        (1 - (theta0 ^ ⌈Real.logb (1 / theta0) (200 / ε)⌉₊) ^ 2) ≤ ε ^ 2 / 10 ^ 4 ∧
    ((1 + ε / 100) + Real.sqrt (2 * (1 + ε / 100) ^ 2 * (ε ^ 2 / 10 ^ 4) +
        12 * (ε ^ 2 / 10 ^ 6) * (1 + (1 + ε / 100)) ^ 2)) /
      Real.sqrt (1 - ε ^ 2 / 10 ^ 6) ≤ 1 + ε := by sorry

end DetANN
