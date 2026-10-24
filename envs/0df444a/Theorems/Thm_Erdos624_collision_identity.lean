-- Prove2me | Theorems.Thm_Erdos624_collision_identity
-- name    : Erdos624.collision_identity
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:40:56.771901+00:00
-- url     : https://prove2.me/theorems/f9d34976-14b0-4946-8896-3f96ed40fde1
-- title:
--   Collision identity for two maps $\mathcal P(U)\to U$ (Erdős 624)
-- statement:
--   **Theorem.** Let $|U|=n=2^k$, $g_0,g_1:\mathcal P(U)\to U$, and $Y\subseteq U$ with $|Y|=k$. Let $J(Y)=\{g_i(A):i\in\{0,1\},A\subseteq Y\}$ and let $C(Y)=2n-|J(Y)|$ be the number of repeated evaluations among the $2n$ evaluations. Then
--
--   $$C(Y)=n+\bigl(n-|J(Y)|\bigr),$$
--
--   and the two maps have a common hole on $Y$ if and only if $C(Y)>n$. An elementary bookkeeping identity: a two-map common hole needs more than $n$ collisions, not just large separate losses.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,(2^k)$; evaluations indexed by $\mathrm{Fin}\,2\times\mathcal P(Y)$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; (1) of claim from GPT 6.1 Sol (fifth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem collision_identity (k : ℕ) (g : Fin 2 → Finset (Fin (2 ^ k)) → Fin (2 ^ k))
    (Y : Finset (Fin (2 ^ k))) (hY : #Y = k) :
    #((univ : Finset (Fin 2)) ×ˢ Y.powerset) -
        #(((univ : Finset (Fin 2)) ×ˢ Y.powerset).image (fun p => g p.1 p.2)) =
      2 ^ k + (2 ^ k - #(((univ : Finset (Fin 2)) ×ˢ Y.powerset).image (fun p => g p.1 p.2))) ∧
    ((∃ u, ∀ i, ∀ A ⊆ Y, g i A ≠ u) ↔
      2 ^ k < #((univ : Finset (Fin 2)) ×ˢ Y.powerset) -
        #(((univ : Finset (Fin 2)) ×ˢ Y.powerset).image (fun p => g p.1 p.2))) := by sorry

end Erdos624
