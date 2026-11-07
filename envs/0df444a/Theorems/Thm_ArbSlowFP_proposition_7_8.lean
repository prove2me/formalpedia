-- Prove2me | Theorems.Thm_ArbSlowFP_proposition_7_8
-- name    : ArbSlowFP.proposition_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:57.886962+00:00
-- url     : https://prove2.me/theorems/8874bc2c-7a96-4257-a699-33ea5c027bd1
-- title:
--   Proposition 7.8 — the new clock and its additional data
-- statement:
--   With phase words and tables from $(59)$, entry action $b_+=a_0$ and counter $v_+=e_g^\top$, the enlarged skew-symmetric payoff matrix $G$ of $(35)$ defines an order-$(k+1)$ clock satisfying Definition 6.2. One may take $Q_{k+1}=Q_{\mathrm{out}}$, $\delta_{0,+}=1$ and $A_{k+1}=A_k+1$.
--
--   **Formalization Note** The clock is `nextClock`, whose fields are these values with priority $(63)$. $Q_{\mathrm{out}}$ is a threshold in the sense of Proposition 7.7. The parameters are as in Proposition 7.6: $T_1\ge T_0$ and every admissible $T_2\ge T_2^\star$.
--
--   Differences from the source:
--   - reading: the clock of the fixed game with T₁, T₂ chosen in §7.2–7.3 → for T₁ ≥ T₀ and every admissible T₂ ≥ T₂⋆; reason: the choices of §7.3 are lower bounds; the printed choice is one instance
--   - encoding: the threshold rule of the new clock is unnamed → an existential Qhat inside the conclusion, with Computable₂ Qhat in IsClock; reason: the proof constructs it (p.62)
--   - encoding: a rational linear map R : im(L) → ℚ^{w×w} with L(R(F)) = F, fixed before T₁ → any ℚ-linear map Rmap on all w×w matrices with L(Rmap F) = F for F ∈ im L (IsSection), quantified before T₀; reason: every linear map on im L extends to the whole space and every such map restricts to one; Rmap is only evaluated on im L at the T₁ ≥ T₀ the statement covers
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.61, Proposition 7.8

import Mathlib
import Definitions.Def_ArbSlowFP_LiftParams

open Matrix

namespace ArbSlowFP

/-- Proposition 7.8, p.61 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). With phase
words and tables from (59), entry action `b₊ = a₀` and counter `v₊ = e⊤_g`, the enlarged skew-symmetric payoff
matrix `G` of (35) defines an order-`(k+1)` clock satisfying Definition 6.2. One may take `Q_{k+1} = Q_out`,
`δ₀,₊ = 1`, `A_{k+1} = A_k + 1`.

**Formalization Note.** `nextClock` fixes those values. `Q_out` is a threshold in the sense of
Proposition 7.7, and `H₊ = A_{k+1} + 3`. -/
theorem proposition_7_8 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) (τ : ℕ) (cref : ℚ) (ℓs : Fin (k + 1) → ℚ) (aP : ι → ℚ)
    (ha : IsAddData d.parent (d.Ak + 3) τ cref ℓs aP)
    (Rmap : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ →ₗ[ℚ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ)
    (hR : IsSection Rmap) :
    let L := d.liftParams τ cref ℓs aP Rmap
    ∃ T0 : ℕ, 1 ≤ T0 ∧ ∀ T1 : ℕ, T0 ≤ T1 →
      ∃ T2s : ℕ, ∀ T2 : ℕ, T2s ≤ T2 → L.IsAdmissible T1 T2 →
        ∃ (Qout : ℕ) (Qhat : ℕ → ℕ → ℕ) (τp : ℕ) (ℓp : Fin (k + 1 + 1) → ℚ)
          (aPp : LiftAct k ι → ℚ),
          L.IsOuterThreshold d.rank d.W T1 T2 Qout ∧
          IsClock (L.nextClock d.rank d.W T1 T2 Qout Qhat) ∧
          IsAddData (L.nextClock d.rank d.W T1 T2 Qout Qhat).parent (d.Ak + 1 + 3) τp (1 / 2) ℓp
            aPp := by sorry

end ArbSlowFP
