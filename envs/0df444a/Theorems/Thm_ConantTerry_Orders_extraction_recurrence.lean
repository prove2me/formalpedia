-- Prove2me | Theorems.Thm_ConantTerry_Orders_extraction_recurrence
-- name    : ConantTerry.Orders.extraction_recurrence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:03.940189+00:00
-- url     : https://prove2.me/theorems/f96147a3-e159-49ec-8298-8c943ac0fe3a
-- title:
--   Claim 1 (Section 3) — existence, base cases and recurrence for T
-- statement:
--   Fix arbitrary sets $X,Y$, a function $f:X\times Y\to[0,1]$, and $\delta>0$. Let $P(k,\ell,t)$ be the universal tree-witness dichotomy of Section 3, with alternatives (I) and (II) as defined in the accompanying definition. Let $T(k,\ell)$ be its least positive qualifying height when one exists.
--
--   1. For all $k,\ell\ge1$, both edge heights exist and
--   $$
--   T(k,1)=T(1,\ell)=1.
--   $$
--   2. For all $k,\ell\ge2$, if $T(k-1,\ell)$ and $T(k,\ell-1)$ exist, then $T(k,\ell)$ exists and
--   $$
--   T(k,\ell)\le T(k-1,\ell)+T(k,\ell-1)+1.
--   $$
--   This is Claim 1 inside the proof of Theorem 1.11, rather than a globally numbered lemma. The base cases and conditional recurrence express the complete claim; existence at all positive pairs follows by induction. The recurrence is a conclusion about the defined minimum and is never a hypothesis of the goal.
--
--   Differences from the source:
--   - encoding: binary words in B_<t, B_≤t and B_t → length-constrained subtypes of List Bool, with false = 0 and true = 1; reason: the empty word, concatenation and initial-segment order are preserved exactly
--   - encoding: [n] = {1,...,n} → Fin n = {0,...,n-1}; reason: subtracting one from every index preserves the order and all diagonal conventions
--   - encoding: f and thresholds take values in [0,1] → f and thresholds take values in the real subtype Set.Icc 0 1; reason: subtype membership enforces precisely the source range without added regularity assumptions
--   - encoding: T(k,l) is undefined when no positive height satisfies P → extractionHeight takes values in WithTop ℕ and is top exactly in that case; existence is expressed by inequality with top; reason: Nat.find is evaluated only with a genuine witness, so finite values are precisely the same least positive heights
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.10, Section 3, proof of Theorem 1.11, Claim 1(a)–(b); proof pp.10–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib
import Definitions.Def_ConantTerry_Orders_extraction_height

namespace ConantTerry.Orders

/-- Section 3, proof of Theorem 1.11, Claim 1, p.10 (proof pp.10–12).
Finiteness of the computed minimum records existence. -/
theorem extraction_recurrence {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ) :
    (∀ (k ℓ : ℕ), 1 ≤ k → 1 ≤ ℓ →
      extractionHeight f δ k 1 = 1 ∧ extractionHeight f δ 1 ℓ = 1) ∧
    (∀ (k ℓ : ℕ), 2 ≤ k → 2 ≤ ℓ →
      extractionHeight f δ (k - 1) ℓ ≠ ⊤ →
      extractionHeight f δ k (ℓ - 1) ≠ ⊤ →
        extractionHeight f δ k ℓ ≠ ⊤ ∧
        extractionHeight f δ k ℓ ≤
          extractionHeight f δ (k - 1) ℓ + extractionHeight f δ k (ℓ - 1) + 1) := by sorry

end ConantTerry.Orders
