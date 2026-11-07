-- Prove2me | Theorems.Thm_ArbSlowFP_theorem_6_1
-- name    : ArbSlowFP.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:51.036896+00:00
-- url     : https://prove2.me/theorems/c941754e-e503-4b58-ab8f-1a5cd3fe98ad
-- title:
--   Theorem 6.1 — one-step construction
-- statement:
--   Every order-$k$ clock satisfying Definition 6.2, $k\ge2$, on $m$ actions can be extended to an order-$(k+1)$ clock on $m+2k+3$ actions satisfying the same definition. The parent matrix is retained as a principal block. The new clock has endpoint counter $v_+=e_g^\top$, prefix margin $\delta_{0,+}=1$, remaining-height constant $A_{k+1}=A_k+1$ and reference gain $c_{\mathrm{ref},+}=1/2$.
--
--   **Formalization Note** The new actions are the type `LiftAct k ι`, whose cardinality is stated; $g$ is its endpoint action.
--
--   Differences from the source:
--   - encoding: "on m + 2k + 3 actions" → the type (ι ⊕ Unit) ⊕ (Fin (k+1) ⊕ Fin (k+1)) with its cardinality stated; reason: the paper adjoins exactly these actions
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.34, Theorem 6.1

import Mathlib
import Definitions.Def_ArbSlowFP_LiftParams

open Matrix

namespace ArbSlowFP

/-- Theorem 6.1, p.34 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). Every order-k clock
satisfying Definition 6.2, `k ≥ 2`, on `m` actions extends to an order-`(k+1)` clock on `m + 2k + 3` actions
satisfying the same definition. The parent matrix is retained as a principal block. The new clock has endpoint
counter `v₊ = e⊤_g`, prefix margin `δ₀,₊ = 1`, remaining-height constant `A_{k+1} = A_k + 1` and reference gain
`cref,₊ = 1/2`.

**Formalization Note.** The action type of the new clock is `LiftAct k ι`, whose cardinality is stated.
The hypothesis `k ≥ 2` is part of `IsClock`. -/
theorem theorem_6_1 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) (τ : ℕ) (cref : ℚ) (ℓs : Fin (k + 1) → ℚ) (aP : ι → ℚ)
    (ha : IsAddData d.parent (d.Ak + 3) τ cref ℓs aP) :
    ∃ dp : ClockData (k + 1) (LiftAct k ι),
      IsClock dp ∧
      (∃ (τp : ℕ) (ℓp : Fin (k + 1 + 1) → ℚ) (aPp : LiftAct k ι → ℚ),
        IsAddData dp.parent (dp.Ak + 3) τp (1 / 2) ℓp aPp) ∧
      Fintype.card (LiftAct k ι) = Fintype.card ι + 2 * k + 3 ∧
      (∀ i j, dp.A (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl j)) = d.A i j) ∧
      dp.v = (fun x => if x = actG then 1 else 0) ∧
      dp.δ0 = 1 ∧
      dp.Ak = d.Ak + 1 := by sorry

end ArbSlowFP
