-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_corollary_4_3
-- name    : BLTCounting.AccuracySpace.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:26.34966+00:00
-- url     : https://prove2.me/theorems/8d956dd0-9155-49e0-84e7-a8474c7007d3
-- title:
--   Isometric compression preserves the rank threshold
-- statement:
--   In the setting of Lemma 4.2, let $Q\in\mathbb C^{|S|\times K}$ satisfy $Q^*Q=I$, and put $F(a)=Q^*\widehat H_S(a)Q$. Then $\mathrm{rank}\,F(c)\le d$, $\|F(f)-F(c)\|_2\le2\eta$, and
--   $$d\ge\#\{j:\lambda_j(F(f))>2\eta\}.$$
--   Any isometric compression therefore keeps the count. The mission's later statements apply this to one specific $Q$.
--
--   **Formalization Note.** Hermitian-ness of $F(f)$ is part of the conclusion, since the eigenvalue count requires it.
--
--   Differences from the source:
--   - generalization: the setting of Theorem 1.2 and the preceding section, including its numerical range for $\eta$ and $n\ge n_0$ → only $\eta>0$, nonempty $S\subseteq\{1,\dots,m-1\}$, the BLT recurrence and the error bound, for every $n$; reason: the conclusion uses no other part of that setting; the source statement is the special case
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Corollary 4.3, printed p. 26 (PDF p. 27)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
import Definitions.Def_BLTCounting_AccuracySpace_Sequences

open Matrix

namespace BLTCounting.AccuracySpace

/-- Corollary 4.3, PDF p. 27: in the setting of Lemma 4.2, for every `Q ∈ ℂ^{|S|×K}` with `Q* Q = I`
and `F(a) = Q* Ĥ_S(a) Q`, one has `rank(F(c)) ≤ d`, `‖F(f) - F(c)‖₂ ≤ 2η`, and equation (31):
`d ≥ #{j : λ_j(F(f)) > 2η}`. -/
theorem corollary_4_3 (n d : ℕ) (c : ℕ → ℂ) (η : ℝ) (hη : 0 < η) (hc : IsBLT d c)
    (herr : coeffErr n sqrtSeq c ≤ η) (S : Finset ℕ) (hSne : S.Nonempty)
    (hS : S ⊆ Finset.Ico 1 ((n + 1) / 2)) (K : ℕ) (Q : Matrix S (Fin K) ℂ)
    (hQ : Qᴴ * Q = 1) :
    (Qᴴ * weightedHankel S c * Q).rank ≤ d ∧
      specNorm (Qᴴ * weightedHankel S sqrtSeq * Q - Qᴴ * weightedHankel S c * Q) ≤ 2 * η ∧
      ∃ hF : (Qᴴ * weightedHankel S sqrtSeq * Q).IsHermitian,
        eigCountAbove hF (2 * η) ≤ d := by sorry

end BLTCounting.AccuracySpace
