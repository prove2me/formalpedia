-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_6_5
-- name    : ArbSlowFP.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:47:53.922444+00:00
-- url     : https://prove2.me/theorems/5d559ed3-6c8d-4664-882e-c55b295c859a
-- title:
--   Lemma 6.5 — solving $PM=D$ and $P^\top X=Q$ simultaneously (38), (39)
-- statement:
--   Suppose $X\in\mathbb Q^{(m+1)\times w}$ and $M\in\mathbb Q^{n\times w}$ have full column rank $w$. The equations $PM=D$, $P^\top X=Q$ are solvable for $P\in\mathbb Q^{(m+1)\times n}$ if and only if
--   $$D^\top X=M^\top Q .$$
--   Moreover, for one-sided inverses with $X^\top L_X=I_w$ and $R_MM=I_w$ and any reference matrix $P_0$, a solution is given by
--   $$D_R=D-P_0M,\quad Q_R=Q-P_0^\top X,\quad P=P_0+D_RR_M+L_X(Q_R^\top-X^\top D_RR_M).$$
--
--   **Formalization Note** $D$, $Q$ are arbitrary matrices of the right shape. The solution clause is under the compatibility identity, as in the page's proof.
--
--   Differences from the source:
--   - generalization: D, Q are the tables of the lift → arbitrary matrices of the right shape, on arbitrary finite index sets; reason: the lemma uses nothing else; the lift is an instance
--   - reading: "a solution to (36) is given explicitly by" → under the hypothesis D⊤X = M⊤Q; reason: the sentence follows the iff, and solvability needs the identity
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), pp.41–42, Lemma 6.5

import Mathlib
import Definitions.Def_ArbSlowFP_tblD

open Matrix

namespace ArbSlowFP

/-- Lemma 6.5, pp.41–42 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…): if `X` and `M`
have full column rank `w`, then `PM = D`, `P⊤X = Q` (36) is solvable for `P` if and only if `D⊤X = M⊤Q`
(38). Moreover, for one-sided inverses `X⊤L_X = I_w`, `R_M M = I_w` and any reference matrix `P₀`, the
matrix (39) is a solution.

**Formalization Note.** The solution clause holds under (38), as the page's proof shows. -/
theorem lemma_6_5 {w : ℕ} {α ρ : Type*} [Fintype α] [Fintype ρ]
    (X : Matrix α (Fin w) ℚ) (M : Matrix ρ (Fin w) ℚ) (hX : X.rank = w) (hM : M.rank = w)
    (D : Matrix α (Fin w) ℚ) (Q : Matrix ρ (Fin w) ℚ) :
    ((∃ P : Matrix α ρ ℚ, P * M = D ∧ Pᵀ * X = Q) ↔ Dᵀ * X = Mᵀ * Q) ∧
    ∀ (LX : Matrix α (Fin w) ℚ) (RM : Matrix (Fin w) ρ ℚ) (P₀ : Matrix α ρ ℚ),
      Xᵀ * LX = 1 → RM * M = 1 → Dᵀ * X = Mᵀ * Q →
        couplingP P₀ D Q X M LX RM * M = D ∧ (couplingP P₀ D Q X M LX RM)ᵀ * X = Q := by sorry

end ArbSlowFP
