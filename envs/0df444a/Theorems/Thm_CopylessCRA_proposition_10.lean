-- Prove2me | Theorems.Thm_CopylessCRA_proposition_10
-- name    : CopylessCRA.proposition_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:41.304197+00:00
-- url     : https://prove2.me/theorems/f5379afe-f4a6-480d-b8da-0185ba540d9e
-- title:
--   Proposition 10 (Compression), p.9 — invertible one-state actions compress to affine coordinate permutations
-- statement:
--   **Standing hypotheses of §3.** $\mathcal Y$ is a monoid acting on $\mathbb Q^r$ by copyless maps $P_y$ with $P_1=\mathrm{id}$ and $P_{yz}=P_z\circ P_y$; its pullbacks $B_y=B_{P_y}$ satisfy $B_{yz}=B_yB_z$. Subspaces $N\subseteq W\subseteq V_r$ are invariant under every $B_y$, $D=W/N$, and $\rho(y)$ is the operator induced by $B_y$ on $D$.
--
--   Assume that $\rho(y)$ is invertible for every $y\in\mathcal Y$. Then there are $k\ge0$, affine coordinate permutations $R_y$ of $\mathbb Q^k$ ($y\in\mathcal Y$), and subspaces $N''\subseteq W''\subseteq V_k$ invariant under every pullback $B_{R_y}$, together with a linear isomorphism
--   $$W''/N''\cong D$$
--   intertwining the operator induced by $B_{R_y}$ with $\rho(y)$ for every $y$.
--
--   The assignment $y\mapsto R_y$ need not be multiplicative.
--
--   Differences from the source:
--   - generalization: copyless maps given by syntactic copyless tuples (§2.1) → maps with multiaffine coordinates and pairwise disjoint variable supports (`IsCopylessMap`); reason: every syntactic copyless tuple is such a map (proved in `Solutions/verification/CopylessCRA_syntactic.lean`), so the statement specializes to the paper's
--   - encoding: $\rho(y)$ invertible → the induced operator on $W/(N\cap W)$ is bijective; reason: same notion on a finite-dimensional space
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Proposition 10, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsRep
import Definitions.Def_CopylessCRA_IsCopylessMap

namespace CopylessCRA

/-- **Proposition 10 (Compression).** Assume that `ρ(y)` is invertible for every `y ∈ 𝒴`. Then there
are `k ≥ 0`, affine coordinate permutations `R_y` of `ℚ^k` (`y ∈ 𝒴`), and subspaces `N'' ⊆ W'' ⊆ V_k`
invariant under every pullback `B_{R_y}`, together with a linear isomorphism `W''/N'' ≅ D`
intertwining the operator induced by `B_{R_y}` with `ρ(y)` for every `y`.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Proposition 10, p.9 (PDF p.11).

**Formalization Note** The standing hypotheses of §3 (p.8): `𝒴` is a monoid acting by
copyless maps `P_y` with `P_1 = id` and `P_{yz} = P_z ∘ P_y`; `N ⊆ W ⊆ V_r` are invariant under every
`B_y = B_{P_y}`; `D = W/N` and `ρ(y)` is the operator induced by `B_y` (`quotOp`). Copyless maps are
taken in the semantic sense (`IsCopylessMap`), a class containing the syntactic one. The assignment `y ↦ R_y` is not required to be multiplicative
(p.9). -/
theorem proposition_10 {r : ℕ} {Y : Type*} [Monoid Y]
    (P : Y → Fin r → MvPolynomial (Fin r) ℚ) (hP : ∀ y, IsCopylessMap (P y))
    (h1 : P 1 = MvPolynomial.X) (hmul : ∀ y z, P (y * z) = compMap (P z) (P y))
    (W N : Submodule ℚ (MvPolynomial (Fin r) ℚ)) (hNW : N ≤ W) (hWV : W ≤ multiaffine r)
    (hW : ∀ y, ∀ h ∈ W, pullback (P y) h ∈ W) (hN : ∀ y, ∀ h ∈ N, pullback (P y) h ∈ N)
    (hinv : ∀ y, Function.Bijective (quotOp (pullback (P y)) W N (hW y) (hN y))) :
    ∃ (k : ℕ) (R : Y → Fin k → MvPolynomial (Fin k) ℚ) (W'' N'' : Submodule ℚ (MvPolynomial (Fin k) ℚ)),
      (∀ y, IsAffineCoordPerm (R y)) ∧ N'' ≤ W'' ∧ W'' ≤ multiaffine k ∧
      ∃ (hW'' : ∀ y, ∀ h ∈ W'', pullback (R y) h ∈ W'')
        (hN'' : ∀ y, ∀ h ∈ N'', pullback (R y) h ∈ N'')
        (e : (W'' ⧸ N''.comap W''.subtype) ≃ₗ[ℚ] (W ⧸ N.comap W.subtype)),
        ∀ y, e.toLinearMap ∘ₗ quotOp (pullback (R y)) W'' N'' (hW'' y) (hN'' y) =
          quotOp (pullback (P y)) W N (hW y) (hN y) ∘ₗ e.toLinearMap := by sorry

end CopylessCRA
