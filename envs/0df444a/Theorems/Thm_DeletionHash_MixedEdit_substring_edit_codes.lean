-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_substring_edit_codes
-- name    : DeletionHash.MixedEdit.substring_edit_codes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:59.06709+00:00
-- url     : https://prove2.me/theorems/b1af5f0c-6ae3-4314-8674-37659876463d
-- title:
--   Theorem 1.2 — substring-edit codes (also Theorem 6.2)
-- statement:
--   For every pair of integers $t\ge2$, $b\ge1$, there is a constant $C_{t,b}$ independent of the alphabet size. For every $q\ge2$ there is a threshold $N(t,b,q)$ such that for every finite alphabet $\Sigma$ of cardinality $q$ and every $n\ge N$, a nonempty finite code $\mathcal C\subseteq\Sigma^n$ corrects at most $t$ $b$-substring edits and satisfies
--   $$\operatorname{red}(\mathcal C)\le(2t-1)\log_q n+C_{t,b}\log_q\log_q n.$$
--   An edit replaces one consecutive substring by a different word, with both lengths at most $b$; the lengths may differ and either may be empty. The code corrects the common-descendant channel with no separation restriction. This single item is Theorem 1.2, proved as Theorem 6.2, and yields ordinary mixed-edit codes at $b=1$.
--
--   Differences from the source:
--   - encoding: length-n words and arbitrary finite alphabets → functions Fin n → α with Fintype α and DecidableEq α; reason: ordered coordinates are equivalent to length-n lists; every finite alphabet admits decidable equality, and no algebraic structure on letters is imposed
--   - encoding: a constant and sufficiently large n → a positive real C and a threshold N≥q^q, before the alphabet type; reason: the proof increases the threshold to n≥q^q so log_q log_q n≥1; increasing C to a positive value preserves the bound
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Theorem 1.2, printed p. 2 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf; same result as Theorem 6.2, printed pp. 19–20 (PDF pp. 21–22)

import Definitions.Def_DeletionHash_MixedEdit_Channel
import Definitions.Def_DeletionHash_MixedEdit_Redundancy

namespace DeletionHash.MixedEdit

universe u

/-- Theorems 1.2 and 6.2: C is chosen before q, and N before the alphabet type. -/
theorem substring_edit_codes (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∃ N : ℕ, q^q ≤ N ∧
      ∀ (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = q →
      ∀ n : ℕ, N ≤ n → ∃ code : Finset (Word α n), code.Nonempty ∧ Corrects b t code ∧
        redundancy q code ≤ ((2*t : ℝ)-1)*logBase q (n : ℝ) + C*logBase q (logBase q (n : ℝ)) := by sorry

end DeletionHash.MixedEdit
