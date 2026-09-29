-- Prove2me | Theorems.Thm_FoundationsML_RademacherVC_sauer_lemma
-- name    : FoundationsML.RademacherVC.sauer_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:15:08.705987+00:00
-- url     : https://prove2.me/theorems/5a749d55-cea3-459f-b472-0b8244d89c76
-- title:
--   Theorem 3.17 — Sauer's lemma
-- statement:
--   **Statement (Theorem 3.17, p. 41, PDF p. 58).** Let $H$ be a hypothesis set with
--   $\mathrm{VCdim}(H)=d$. Then, for all $m\in\mathbb N$,
--   $$\Pi_H(m) \le \sum_{i=0}^{d}\binom{m}{i}.$$
--
--   This is the chapter's central combinatorial result, proved by a genuine induction on
--   `m + d` (splitting `H`'s restriction to `S` into two families `G₁`, `G₂` on the last
--   point), bounding the growth function — which could a priori be as large as `2^m` — by a
--   polynomial in `m` of degree `d` once the VC-dimension is finite.
--
--   **Formalization Note.** `Finset.range (d+1)` sums `i = 0,…,d`, matching
--   $\sum_{i=0}^d\binom{m}{i}$ exactly; `Nat.choose m i` is $\binom{m}{i}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 41, Theorem 3.17 (PDF p. 58)

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim

namespace FoundationsML.RademacherVC

/-- Theorem 3.17 (Sauer's lemma; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 41, PDF p. 58). Let `H` be a hypothesis set with
`VCdim(H) = d`. Then, for all `m ∈ ℕ`, `Π_H(m) ≤ ∑_{i=0}^{d} C(m,i)`. -/
theorem sauer_lemma
    {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (m : ℕ) :
    GrowthFunction H m ≤ ∑ i ∈ Finset.range (d + 1), Nat.choose m i := by sorry

end FoundationsML.RademacherVC
