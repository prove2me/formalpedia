-- Prove2me | Theorems.Thm_ArbSlowFP_proposition_4_4
-- name    : ArbSlowFP.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:24.810926+00:00
-- url     : https://prove2.me/theorems/666dbb4e-f624-4b4c-b297-e9a6d25e9587
-- title:
--   Proposition 4.4 — recursive family starting from RPS
-- statement:
--   There is a sequence of order-$k$ clocks, one for each integer $k\ge2$, whose order-2 member is the RPS clock of Proposition 5.1. If its order-$k$ member has $m_k$ actions, then its order-$(k+1)$ member has $m_k+2k+3$ actions and retains the parent matrix as a principal block. Its new phase word is $B(q)A(q+1)$, its entry height is $\zeta(q)$, and its new endpoint counter is $e_g^\top$. The constants satisfy $\delta_{0,k+1}=1$ and $A_{k+1}=A_k+1$.
--
--   The closed forms $m_k=(k+1)^2-6$ and $A_k=k-1$ of $(24)$ are part of the statement.
--
--   **Formalization Note** The family is indexed by $j$ with $k=j+2$, on the recursively defined action types `FamAct j`. Each step is a lift with explicit parameters, carrying Definition 6.2 for the parent. The action count $m_k+2k+3$ follows from the type and the closed form.
--
--   Differences from the source:
--   - encoding: a sequence of clocks, one for each k ≥ 2 → a family indexed by j with k = j + 2, on the action types FamAct j; reason: the action type changes with k; same family
--   - generalization: the closed forms (24) are stated at p.31 in the main proof → included in the statement; reason: they follow from the proposition, whose printed clauses are all kept
--   - generalization: the new phase word B(q)A(q+1), entry height ζ(q) and counter e⊤_g of each step → each step is the lift of §6–7 with explicit parameters (τ, cref, ℓ∗, a_P, Rmap, T₁, T₂), with IsSection, the Definition 6.2 data of every member, admissibility, and G as the new matrix; reason: these are the objects the printed clauses name; the proof builds the family by Theorem 6.1, so every member carries them
--   - encoding: a rational linear map R : im(L) → ℚ^{w×w} with L(R(F)) = F, fixed before T₁ → any ℚ-linear map Rmap on all w×w matrices with L(Rmap F) = F for F ∈ im L (IsSection), chosen with each step; reason: every linear map on im L extends to the whole space and every such map restricts to one; the lift evaluates Rmap only on im L
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.28, Proposition 4.4; (24), p.31

import Mathlib
import Definitions.Def_ArbSlowFP_rpsClockData
import Definitions.Def_ArbSlowFP_LiftParams

open Matrix

namespace ArbSlowFP

/-- Proposition 4.4, p.28 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). There is a sequence
of order-k clocks, `k ≥ 2`, whose order-2 member is the RPS clock of Proposition 5.1. If its order-k member has
`m_k` actions, its order-`(k+1)` member has `m_k + 2k + 3` actions and retains the parent matrix as a principal
block; its new phase word is `B(q)A(q+1)`, its entry height is `ζ(q)`, and its new endpoint counter is `e⊤_g`;
`δ₀,_{k+1} = 1` and `A_{k+1} = A_k + 1`.

**Formalization Note.** The family is indexed by `j` with `k = j + 2`, on the action types `FamAct j`, and each
step is a lift with explicit parameters. The count `m_k = (k+1)² - 6` and `A_k = k - 1` of (24), p.31, are
included. -/
theorem proposition_4_4 :
    ∃ d : ∀ j : ℕ, ClockData (j + 2) (FamAct j),
      d 0 = rpsClockData ∧
      (∀ j, IsClock (d j)) ∧
      (∀ j, Fintype.card (FamAct j) = (j + 3) ^ 2 - 6) ∧
      (∀ j, (d j).Ak = (j : ℚ) + 1) ∧
      ∀ j, ∃ (τ : ℕ) (cref : ℚ) (ℓs : Fin (j + 2 + 1) → ℚ) (aP : FamAct j → ℚ)
          (Rmap : Matrix (Fin (j + 2 + 1)) (Fin (j + 2 + 1)) ℚ →ₗ[ℚ]
            Matrix (Fin (j + 2 + 1)) (Fin (j + 2 + 1)) ℚ) (T1 T2 : ℕ),
        IsSection Rmap ∧
        IsAddData (d j).parent ((d j).Ak + 3) τ cref ℓs aP ∧
        let L := (d j).liftParams τ cref ℓs aP Rmap
        L.IsAdmissible T1 T2 ∧
        (d (j + 1)).A = L.G T1 T2 ∧
        (∀ x y, (d (j + 1)).A (Sum.inl (Sum.inl x)) (Sum.inl (Sum.inl y)) = (d j).A x y) ∧
        (∀ q, (d (j + 1)).Q ≤ q → (d (j + 1)).W q = L.nextWord (d j).W T1 T2 q) ∧
        (d (j + 1)).R (d (j + 1)).b = L.zeta T1 ∧
        (d (j + 1)).v = (fun x => if x = actG then 1 else 0) ∧
        (d (j + 1)).δ0 = 1 ∧
        (d (j + 1)).Ak = (d j).Ak + 1 := by sorry

end ArbSlowFP
