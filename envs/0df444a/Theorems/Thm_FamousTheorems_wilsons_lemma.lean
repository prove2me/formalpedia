-- Prove2me | Theorems.Thm_FamousTheorems_wilsons_lemma
-- name    : FamousTheorems.wilsons_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:51:57.329726+00:00
-- url     : https://prove2.me/theorems/82c937d3-2a17-431f-b973-31e7c8993994
-- title:
--   Wilson's theorem
-- statement:
--   **Wilson's theorem.**
--
--   For a prime $p$,
--   $$(p-1)! \;\equiv\; -1 \pmod p .$$
--
--   Pairing each residue in $\{1,\dots,p-1\}$ with its inverse leaves only the self-inverse elements
--   $1$ and $p-1$, whose product is $-1$; all other residues cancel in pairs. The converse also
--   holds, so this is a characterisation of primes — though a useless primality test, since
--   computing $(p-1)! \bmod p$ is far harder than trial division.
--
--   Stated by Ibn al-Haytham around 1000, conjectured again by Wilson, and first proved by Lagrange
--   in 1771.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem wilsons_lemma : ∀ (p : ℕ) [Fact (Nat.Prime p)], (((p - 1).factorial : ℕ) : ZMod p) = -1 := by sorry

end FamousTheorems
