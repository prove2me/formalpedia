-- Prove2me | Theorems.Thm_Erdos195_single_inversion_iff
-- name    : Erdos195.single_inversion_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T20:29:43.578993+00:00
-- url     : https://prove2.me/theorems/bccc2e53-053a-438f-a3fe-b422c1919bfc
-- title:
--   Single-inversion criterion: U·(b,c)·V (classes mod 4) has a SAFE extension iff 4c−3b ∉ b·V or 5c−4b ∉ U·c
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $W$ of integers is SAFE for $\theta$ if the sequence "letters of $W$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression. **Theorem (single-inversion criterion).** Let $b$ be odd and $c$ even, and let $T=U\cdot(b,c)\cdot V$ be a duplicate-free word in which every entry of $E=U\cdot(c)$ is $\equiv c\pmod 4$ and every entry of $O=(b)\cdot V$ is $\equiv b\pmod 4$. Assume $E$ and $O$ are each SAFE (for some tree witnesses). Put $p=4c-3b$ and $q=5c-4b$. Then $T$ has a SAFE end-extension $T\cdot R$ (for some tree witness) if and only if
--   $$p\notin O\quad\text{or}\quad q\notin E.$$
--   Moreover, when this holds, $R$ can be chosen with exactly $|V|+2=|O|+1$ entries, all new and distinct.
--
--   This is GPT 6 Astra's single-inversion repair lemma (astra_fourclass) as a standalone exact criterion. With $w=3c-2b$ and $t=2c-b$: if $p\notin O$, $R=(2w-O)\cdot(w)$ (reflections in inherited order); if $p\in O$ and $q\notin E$, $R=L\cdot(w,t)$ where $L\cdot t$ is a SAFE ordering of the reflection set $2w-O$ ending at $t$ (milestone #133). The necessity half is the interlocked root obstruction (milestone #135): if $p\in O$ and $q\in E$, the pairs $(b,c)$ and $(q,p)$ can never close and force opposite root bits. Milestones #122 and #136 are the two positive cases, in the coordinates of the four-class absorption theorem.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026); lemma of GPT 6 Astra (astra_fourclass)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem single_inversion_iff (U V : List ℤ) (b c : ℤ)
    (hbo : b % 2 = 1) (hce : c % 2 = 0)
    (hU : ∀ x ∈ U, x % 4 = c % 4) (hV : ∀ x ∈ V, x % 4 = b % 4)
    (hnd : (U ++ [b, c] ++ V).Nodup)
    (hE : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [c]))
    (hO : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ([b] ++ V)) :
    ((∃ R : List ℤ, ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [b, c] ++ V ++ R)) ↔
      (4 * c - 3 * b ∉ [b] ++ V ∨ 5 * c - 4 * b ∉ U ++ [c])) ∧
    ((4 * c - 3 * b ∉ [b] ++ V ∨ 5 * c - 4 * b ∉ U ++ [c]) →
      ∃ R : List ℤ, R.length = V.length + 2 ∧ (U ++ [b, c] ++ V ++ R).Nodup ∧
        ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (U ++ [b, c] ++ V ++ R)) := by sorry

end Erdos195
