-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_6_4
-- name    : ArbSlowFP.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:48:00.200557+00:00
-- url     : https://prove2.me/theorems/22fedb14-4d6c-4941-ad8a-212163f44de7
-- title:
--   Lemma 6.4 — the two coupling equations give the next phase-entry scores (37)
-- statement:
--   With the tables $(28)$ and $(35)$, the equations $PM=D$ and $P^\top X=Q$ hold if and only if the combined word with count table $\mathrm{col}(X,M)$ changes the full score table from $U=\mathrm{col}(S,V)$ to $UT$. Equivalently,
--   $$G\begin{pmatrix}X\\M\end{pmatrix}=UN .$$
--
--   This is an identity of coefficient tables; whether the word is actually played is a separate question.
--
--   **Formalization Note** The change of the score table is $U+G\,\mathrm{col}(X,M)=UT$.
--
--   Differences from the source:
--   - generalization: the tables (28) and (35) of a parent clock with n = 2r reset actions → any bare parent tables, parameters and any finite reset index set, with arbitrary M, J, P; reason: the lemma is a table identity; the paper's case is an instance
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.41, Lemma 6.4

import Mathlib
import Definitions.Def_ArbSlowFP_tblD

open Matrix

namespace ArbSlowFP

/-- Lemma 6.4, p.41 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…): with the tables
(28) and (35), `PM = D` and `P⊤X = Q` hold if and only if the combined word with count table `col(X, M)`
changes `U = col(S, V)` to `UT`; equivalently, `G col(X, M) = UN` (37). The lemma is an identity of
coefficient tables for every `M`, `J`, `P`.

**Formalization Note.** The conclusion is an equality of the block tables on `(ι ⊕ Unit) ⊕ ρ`, and the
middle clause is written as `U + G col(X, M) = UT`. The reset index type `ρ` is an arbitrary finite
type. -/
theorem lemma_6_4 {k : ℕ} {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
    (Pa : Parent k ι) (H : ℚ) (τ : ℕ) (c δ : ℚ) (M : Matrix ρ (Fin (k + 1)) ℚ)
    (J : Matrix ρ ρ ℚ) (P : Matrix (ι ⊕ Unit) ρ ℚ) :
    let G := liftG Pa.GO P J
    let ζ := Pa.zeta H τ c
    let U := Matrix.fromRows (Pa.S H τ c δ) (resetV ζ J M)
    let XM := Matrix.fromRows (Pa.X τ) M
    ((P * M = Pa.D H τ c δ ∧ Pᵀ * Pa.X τ = resetQ ζ J M) ↔ U + G * XM = U * shiftT (k + 1)) ∧
    ((P * M = Pa.D H τ c δ ∧ Pᵀ * Pa.X τ = resetQ ζ J M) ↔ G * XM = U * shiftN (k + 1)) := by sorry

end ArbSlowFP
