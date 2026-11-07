-- Prove2me | Theorems.Thm_ArbSlowFP_proposition_7_4
-- name    : ArbSlowFP.proposition_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:37.877926+00:00
-- url     : https://prove2.me/theorems/3ea6ee41-af50-4de0-839f-f5f727c4e3dc
-- title:
--   Proposition 7.4 — exact solution of the scalar compatibility tests, (49)
-- statement:
--   Let an order-$k$ clock carry the additional data of Definition 6.2 and fix the linear section $\mathcal R$ of $L$. For all sufficiently large $T_1$, the gain $c$ of $(47)$ (or $c=c_{\mathrm{ref}}$ for odd $k$) lies in $(0,1)$. The argument of $\mathcal R$ in $(48)$ satisfies every compatibility test, so $E$ is a rational solution of
--   $$E-E^\top B=D^\top X-\ell^\top\psi .$$
--   Moreover, as $T_1\to\infty$ with the parent data fixed, $c-c_{\mathrm{ref}}=O(T_1^{-1})$ and $E-T_1E_0=O(1)$.
--
--   Differences from the source:
--   - encoding: O(·) as T₁ → ∞ with parent data fixed → explicit constants K, T₀ quantified before T₁ and T₂, with the norm (45) written as two inequalities; reason: this is the definition of O printed on p.49
--   - encoding: "sufficiently large T₁" and the fixed section R → T₀ quantified after R; reason: p.49 fixes R, depending only on k, before T₁
--   - encoding: a rational linear map R : im(L) → ℚ^{w×w} with L(R(F)) = F, fixed before T₁ → any ℚ-linear map Rmap on all w×w matrices with L(Rmap F) = F for F ∈ im L (IsSection), quantified before T₀; reason: every linear map on im L extends to the whole space and every such map restricts to one; Rmap is only evaluated on im L at the T₁ ≥ T₀ the statement covers
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.50, Proposition 7.4

import Mathlib
import Definitions.Def_ArbSlowFP_LiftParams

open Matrix

namespace ArbSlowFP

/-- Proposition 7.4, p.50 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). For an
order-k clock with the additional data of Definition 6.2 and a fixed section `R` of `L`: for all
sufficiently large `T₁`, the gain `c` of (47) (or `c = cref` for odd `k`) lies in `(0, 1)`; the argument
of `R` in (48) satisfies every compatibility test, so that `E - E⊤B = D⊤X - ℓ⊤ψ` (40); and (49):
`c - cref = O(T₁⁻¹)`, `E - T₁E₀ = O(1)` as `T₁ → ∞` with the parent data fixed.

**Formalization Note.** `O` is written out with the constants `K` and `T₀`, in the norm (45). -/
theorem proposition_7_4 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) (τ : ℕ) (cref : ℚ) (ℓs : Fin (k + 1) → ℚ) (aP : ι → ℚ)
    (ha : IsAddData d.parent (d.Ak + 3) τ cref ℓs aP)
    (Rmap : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hR : IsSection Rmap) :
    let L := d.liftParams τ cref ℓs aP Rmap
    ∃ (K : ℚ) (T0 : ℕ), 1 ≤ T0 ∧ ∀ T1 : ℕ, T0 ≤ T1 →
      0 < L.gain T1 ∧ L.gain T1 < 1 ∧
      (∀ h, Even h → k ≤ h → h ≤ 2 * k → frob (testZ k h) (L.Earg T1) = 0) ∧
      opL (L.E T1) = (L.D T1)ᵀ * L.P.X τ - Matrix.vecMulVec (L.ell T1) (L.psi T1) ∧
      |L.gain T1 - cref| ≤ K / (T1 : ℚ) ∧
      NormStarLE (L.E T1 - (T1 : ℚ) • L.E0) K := by sorry

end ArbSlowFP
