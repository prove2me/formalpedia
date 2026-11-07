-- Prove2me | Theorems.Thm_ArbSlowFP_proposition_7_6
-- name    : ArbSlowFP.proposition_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:57:00.780199+00:00
-- url     : https://prove2.me/theorems/d7974dd6-f9c1-4001-af17-0ccac3f58cc3
-- title:
--   Proposition 7.6 — positive weights for the next order
-- statement:
--   Fix a sufficiently large scale $T_1$ as in Lemma 7.5. There is a sufficiently large integer $T_2\ge\max\{T_1,\upsilon_k\}$ such that the rotated tables $R_+$, $C_+$ of $(59)$ satisfy the positive-weight condition of Definition 6.2(ii) at order $k+1$, with reference gain $c_{\mathrm{ref},+}=1/2$. This choice preserves the reset equations, signs and margins of Lemma 7.5. The next scale $\tau_+$ and correction $\ell_{*,+}$, which satisfy Definition 6.2(i), are fixed before $T_2$, since the data of Lemma 7.2 are independent of $T_2$:
--   $$R_+^\top C_+=S_{\mathrm{mid}}^\top XT+\zeta^\top\ell-E^\top,\quad \mathbf 1^\top C_+=\mathbf 1^\top XT+\ell,\quad (R_+)_{a_0,:}=\zeta,\quad (C_+)_{g,:}=e_{0,w}^\top .$$
--
--   **Formalization Note** "Sufficiently large" is: there is $T_2^\star$ such that the conclusion holds for every admissible $T_2\ge T_2^\star$. Definition 6.2 at order $k+1$ is at the baseline $H_+=A_k+4$.
--
--   Differences from the source:
--   - reading: "There is a sufficiently large integer T₂" → there is T₂⋆ such that every admissible T₂ ≥ T₂⋆ works, with (τ₊, ℓ∗,₊) fixed before T₂; reason: (62) gives a lower bound on T₂, with (τ₊, ℓ∗,₊) computed from T₂-independent data
--   - generalization: the positive-weight condition of Definition 6.2(ii) → IsAddData at H₊ = A_k + 4, cref,₊ = 1/2 (also Definition 6.2(i)), with (60) and ResetBoundsAt; reason: the proof states "This supplies the positive-weight and scalar-test data", and (60) is displayed there; the printed conclusion is part of this one
--   - encoding: a rational linear map R : im(L) → ℚ^{w×w} with L(R(F)) = F, fixed before T₁ → any ℚ-linear map Rmap on all w×w matrices with L(Rmap F) = F for F ∈ im L (IsSection), quantified before T₀; reason: every linear map on im L extends to the whole space and every such map restricts to one; Rmap is only evaluated on im L at the T₁ ≥ T₀ the statement covers
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.56, Proposition 7.6, eq. (60)

import Mathlib
import Definitions.Def_ArbSlowFP_LiftParams

open Matrix

namespace ArbSlowFP

/-- Proposition 7.6, p.56 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). Fix a
sufficiently large `T₁` as in Lemma 7.5. There is a sufficiently large integer `T₂ ≥ max{T₁, υ_k}` such that
the rotated tables (59) satisfy Definition 6.2 (ii) at order `k + 1` with `cref,₊ = 1/2`, and this preserves
the reset equations, signs and margins of §7.2. The next scale `τ₊` and correction `ℓ∗,₊`, which satisfy
Definition 6.2 (i), come from data independent of `T₂` (60).

**Formalization Note.** "Sufficiently large" is `∃ T₂⋆, ∀ T₂ ≥ T₂⋆`, given by (62), with `(τ₊, ℓ∗,₊)` chosen
before `T₂`. The conclusion is `IsAddData` at `H₊ = A_k + 4`, with (60) and `ResetBoundsAt`. -/
theorem proposition_7_6 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) (τ : ℕ) (cref : ℚ) (ℓs : Fin (k + 1) → ℚ) (aP : ι → ℚ)
    (ha : IsAddData d.parent (d.Ak + 3) τ cref ℓs aP)
    (Rmap : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hR : IsSection Rmap) :
    let L := d.liftParams τ cref ℓs aP Rmap
    ∃ T0 : ℕ, 1 ≤ T0 ∧ ∀ T1 : ℕ, T0 ≤ T1 →
      ∃ (τp : ℕ) (ℓp : Fin (k + 1 + 1) → ℚ) (T2s : ℕ), ∀ T2 : ℕ, T2s ≤ T2 → L.IsAdmissible T1 T2 →
        (∃ aPp : LiftAct k ι → ℚ,
          IsAddData (L.nextParent T1 T2) (d.Ak + 4) τp (1 / 2) ℓp aPp) ∧
        (L.Rplus T1 T2)ᵀ * L.Cplus T1 T2 =
          (L.Smid T1)ᵀ * (L.P.X τ * shiftT (k + 1)) + Matrix.vecMulVec (L.zeta T1) (L.ell T1)
            - (L.E T1)ᵀ ∧
        (1 : LiftAct k ι → ℚ) ᵥ* L.Cplus T1 T2 =
          (1 : ι ⊕ Unit → ℚ) ᵥ* (L.P.X τ * shiftT (k + 1)) + L.ell T1 ∧
        L.Rplus T1 T2 actA0 = L.zeta T1 ∧
        L.Cplus T1 T2 actG = e0Row (k + 1) ∧
        L.ResetBoundsAt T1 T2 := by sorry

end ArbSlowFP
