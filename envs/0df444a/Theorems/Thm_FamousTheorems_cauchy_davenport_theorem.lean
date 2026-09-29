-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_davenport_theorem
-- name    : FamousTheorems.cauchy_davenport_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:27:05.583121+00:00
-- url     : https://prove2.me/theorems/e31db4ca-9d48-4e26-bca3-e94580ffa358
-- title:
--   The Cauchy–Davenport theorem
-- statement:
--   **The Cauchy–Davenport theorem.** Let $p$ be a prime and $s,t$ nonempty subsets of $\mathbb Z/p\mathbb Z$. Then
--   $$|s+t|\ge\min\big(p,\ |s|+|t|-1\big).$$
--
--   It is the founding result of additive combinatorics in groups of prime order. Arithmetic progressions with a common difference show the bound is sharp, and Vosper's theorem describes the equality cases. Generalisations include Kneser's theorem and the Erdős–Heilbronn conjecture (Dias da Silva–Hamidoune).
--
--   **Formalization note.** Mathlib's `ZMod.cauchy_davenport`, with pointwise sumset `s + t` of finsets of `ZMod p`. Subtraction is on `ℕ`, harmless since $|s|+|t|\ge2$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ZMod.cauchy_davenport`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped Pointwise

theorem cauchy_davenport_theorem {p : ℕ} (hp : p.Prime) {s t : Finset (ZMod p)} (hs : s.Nonempty) (ht : t.Nonempty) :
    min p (s.card + t.card - 1) ≤ (s + t).card := by sorry

end FamousTheorems
