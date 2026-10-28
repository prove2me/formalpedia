-- Prove2me | Theorems.Thm_Erdos624_subsetSum_finite
-- name    : Erdos624.subsetSum_finite
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:41:07.46018+00:00
-- url     : https://prove2.me/theorems/352b8e9d-f429-4433-9f40-d943222d7721
-- title:
--   Image bound for subset-sum-factor maps on a well-chosen $k$-set (Erdős 624)
-- statement:
--   Let $U$ be a set of $n=2^k$ elements, $V=\mathbb F_2^k$, and consider $r$ *subset-sum-factor* maps
--
--   $$g_i(A)=\psi_i\Bigl(\sum_{a\in A}v_i(a)\Bigr),\qquad v_i:U\to V,\ \psi_i:V\to U\ \text{arbitrary}.$$
--
--   **Theorem.** Let $d,t\ge0$ with $2td\le k$ and $\binom{n-2t(d-1)}{t}>n^r$. Then there is a $k$-set $Y\subseteq U$ with
--
--   $$2^d\,\bigl|\{g_i(A):A\subseteq Y\}\bigr|\le 2^k\ \text{ for every } i,\qquad 2^d\,\Bigl|\bigcup_{i<r}\{g_i(A):A\subseteq Y\}\Bigr|\le r\,2^k.$$
--
--   In particular, if $r<2^d$ the $r$ maps have a common hole on $Y$. The set $Y$ contains $d$ disjoint nonempty sets of size $\le 2t$ whose $v_i$-sums vanish simultaneously for all $i$; flipping by them preserves every $g_i$, so every fibre of $g_i$ on $\mathcal P(Y)$ has at least $2^d$ elements.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,(2^k)$, $V$ is `Fin k → ZMod 2`, tracks indexed by $\mathrm{Fin}\,r$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; (13)–(15) of claim from GPT 6.1 Sol (fifth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem subsetSum_finite (k r d t : ℕ) (hk : 2 * t * d ≤ k)
    (hc : (2 ^ k) ^ r < (2 ^ k - 2 * t * (d - 1)).choose t)
    (v : Fin r → Fin (2 ^ k) → (Fin k → ZMod 2)) (ψ : Fin r → (Fin k → ZMod 2) → Fin (2 ^ k)) :
    ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧
      (∀ i, 2 ^ d * #(Y.powerset.image (fun A => ψ i (∑ a ∈ A, v i a))) ≤ 2 ^ k) ∧
      2 ^ d * #(((univ : Finset (Fin r)) ×ˢ Y.powerset).image
        (fun p => ψ p.1 (∑ a ∈ p.2, v p.1 a))) ≤ r * 2 ^ k := by sorry

end Erdos624
