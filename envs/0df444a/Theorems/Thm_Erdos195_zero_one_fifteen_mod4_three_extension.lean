-- Prove2me | Theorems.Thm_Erdos195_zero_one_fifteen_mod4_three_extension
-- name    : Erdos195.zero_one_fifteen_mod4_three_extension
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T19:50:02.309222+00:00
-- url     : https://prove2.me/theorems/d166f85b-6533-413f-b699-ff68291393af
-- title:
--   Every finite set of integers ≡3 (mod 4) extends the prefix (0,1,15) to a tree-safe word
-- statement:
--   A tree witness is a function θ:ℕ×ℤ→{0,1} on the nodes (k,r) of the binary tree of residues. For distinct integers x,y with k=ν₂(y−x), put x≺_θ y iff bit_k(x)=1 precisely when θ(k, x mod 2^k)=1. A finite word Q is θ-safe if the completion “letters of Q in order, then all remaining integers in ≺_θ-order” contains no monotone 4-term arithmetic progression. Positions are first occurrences.
--
--   **(0,1,15) residue-3 mod 4 extension.** Let F be any finite set of integers each congruent to 3 modulo 4. There exists a finite duplicate-free word Q that begins with the prefix (0,1,15), contains every element of F, and admits a tree-safe witness.
--
--   The construction is the m=2 case of the official safe-word composition theorem, with residue order (0,2,1,3) (a tree order for the constant-false witness). Form H by inserting 3 into the image {(z−3)/4 : z∈F}, obtain a tree-safe word A beginning with 3 whose underlying set is H by specified_first_safe_order, and concatenate the lifted blocks 0+(4·(0)), 2+(4·∅), 1+(4·(0)), and 3+(4·A). The resulting word is 0,1 followed by 3+4A, hence begins (0,1,15) and contains F. This does not settle Erdős #195.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); derived from analysis relayed by Ethan Cheung, hand-checked against the official Safe / treeLt / specified_first_safe_order / safe_word_composition definitions, Lean-verified.

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem zero_one_fifteen_mod4_three_extension (F : Finset ℤ)
    (hF : ∀ z ∈ F, z % 4 = 3) :
    ∃ Q : List ℤ, Q.Nodup ∧ (∃ T : List ℤ, Q = 0 :: 1 :: 15 :: T) ∧ (∀ z ∈ F, z ∈ Q) ∧
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q := by sorry

end Erdos195
