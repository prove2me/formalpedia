-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_mixed_edit_codes
-- name    : DeletionHash.MixedEdit.mixed_edit_codes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:49.816736+00:00
-- url     : https://prove2.me/theorems/18e1bad8-9616-4c93-beec-5ad2af17d8ce
-- title:
--   Theorem 1.1 — mixed-edit codes with leading coefficient 2t−1
-- statement:
--   For every integer $t\ge2$, there is a constant $C_t$ independent of the alphabet size. For every $q\ge2$ there is a threshold $N(t,q)$ such that for every finite alphabet $\Sigma$ with $|\Sigma|=q$ and every $n\ge N$, there is a nonempty finite code $\mathcal C\subseteq\Sigma^n$ correcting any combination of at most $t$ insertions, deletions and substitutions in total, with
--   $$\operatorname{red}(\mathcal C)\le(2t-1)\log_q n+C_t\log_q\log_q n.$$
--   Every intermediate or received word may have any finite length. Each of the three ordinary operations costs one, end insertions are allowed, and substitution must change the letter. The code's correction property prohibits a common word obtainable from two distinct codewords within their budgets. This is the headline theorem, including arbitrary finite alphabets and the leading coefficient $2t-1$.
--
--   Differences from the source:
--   - encoding: length-n words and arbitrary finite alphabets → functions Fin n → α with Fintype α and DecidableEq α; reason: ordered coordinates are equivalent to length-n lists; every finite alphabet admits decidable equality, and no algebraic structure on letters is imposed
--   - encoding: a constant and sufficiently large n → a positive real C and a threshold N≥q^q, before the alphabet type; reason: the proof increases the threshold to n≥q^q so log_q log_q n≥1; increasing C to a positive value preserves the bound
--   - encoding: ordinary unit-cost insertion, deletion and proper substitution → the concrete bounded-substring channel at b=1; reason: nonempty proper replacements with both lengths at most one have exactly the three ordinary forms; no edit-distance equivalence is assumed
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Theorem 1.1, printed p. 2 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Channel
import Definitions.Def_DeletionHash_MixedEdit_Redundancy

namespace DeletionHash.MixedEdit

universe u

/-- Theorem 1.1: C is chosen before q, and N before the alphabet type. -/
theorem mixed_edit_codes (t : ℕ) (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∃ N : ℕ, q^q ≤ N ∧
      ∀ (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
      ∀ n : ℕ, N ≤ n → ∃ code : Finset (Word α n), code.Nonempty ∧ Corrects 1 t code ∧
        redundancy q code ≤ ((2*t : ℝ)-1)*logBase q (n : ℝ) + C*logBase q (logBase q (n : ℝ)) := by sorry

end DeletionHash.MixedEdit
