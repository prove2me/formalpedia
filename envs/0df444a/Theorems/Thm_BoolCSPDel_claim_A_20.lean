-- Prove2me | Theorems.Thm_BoolCSPDel_claim_A_20
-- name    : BoolCSPDel.claim_A_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:30.999994+00:00
-- url     : https://prove2.me/theorems/d3c35d5e-8849-4fae-87bf-883b1dd0730d
-- title:
--   Claim A.20 — $h$-wise matrix concentration
-- statement:
--   Let $A_i\succeq0$ be $D\times D$ real matrices with $\sum_iA_i\preceq3I$ and $\|A_i\|_{\mathrm{op}}\le\tau$. Let the indicators $\xi_i$ be $h$-wise independent with mean $1/4$, where $h$ is even and $h\ge\ln(4D^2/\beta)$. If $0<\varepsilon_s\le1$ and $\tau\le\varepsilon_s^2/(1000h)$, then
--
--   $$\Pr\Bigl[\Bigl\|\sum_i(4\xi_i-1)A_i\Bigr\|_{\mathrm{op}}>\varepsilon_s\Bigr]\le\beta.$$
--
--   This controls one sampling step of the decoder with short seeds.
--
--   Differences from the source:
--   - encoding: β and D unconstrained on the page → 0 < β and 1 ≤ D; reason: ln(4D²/β) needs a positive argument, and D is a matrix dimension
--   - encoding: the indicators ξ_i → a law on {0,1}^ι, ι a finite index type; reason: a finite family, as the row set [m]
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Claim A.20, p.61

import Mathlib
import Definitions.Def_BoolCSPDel_Params
import Definitions.Def_BoolCSPDel_Mono

namespace BoolCSPDel

/-- **Claim A.20 (`h`-wise matrix concentration).** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Claim A.20, p.61.

Let `A_i ⪰ 0`, `Σ_i A_i ⪯ 3I`, `‖A_i‖_op ≤ τ`, and let the indicators `ξ_i` be `h`-wise independent with mean `1/4`,
with `h` even and `h ≥ ln(4D²/β)`. If `0 < ε_s ≤ 1` and `τ ≤ ε_s²/(1000h)`, then
`Pr[‖Σ_i(4ξ_i − 1)A_i‖_op > ε_s] ≤ β`.

**Formalization Note.** Operator norm of the Euclidean operator, the largest absolute eigenvalue on symmetric
matrices (§3.5, p.23). At `h = 0`, which the page does not exclude, the hypothesis forces `β ≥ 4D²` and the
claim is trivial. -/
theorem claim_A_20 {ι : Type} [Fintype ι] {D : ℕ} (hD : 1 ≤ D)
    (A : ι → Matrix (Fin D) (Fin D) ℝ) (hA : ∀ i, (A i).PosSemidef)
    (hsum : LoewnerLE (∑ i, A i) ((3 : ℝ) • (1 : Matrix (Fin D) (Fin D) ℝ)))
    (τ : ℝ) (hτ : ∀ i, ‖Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℝ) (A i)‖ ≤ τ)
    (ξ : PMF (ι → Bool)) (h : ℕ) (hξ : IsHWiseQuarter ξ h) (hh : Even h) (β : ℝ) (hβ : 0 < β)
    (hhβ : Real.log (4 * (D : ℝ) ^ 2 / β) ≤ h) (εs : ℝ) (hε : 0 < εs) (hε' : εs ≤ 1)
    (hτε : τ ≤ εs ^ 2 / (1000 * (h : ℝ))) :
    ξ.toMeasure {x | εs < ‖Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℝ)
      (∑ i, (4 * (if x i then (1 : ℝ) else 0) - 1) • A i)‖} ≤ ENNReal.ofReal β := by sorry

end BoolCSPDel
