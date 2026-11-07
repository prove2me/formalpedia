-- Prove2me | Theorems.Thm_ContinualCounting_lemma_6_psi_orthonormal
-- name    : ContinualCounting.lemma_6_psi_orthonormal
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:38.599274+00:00
-- url     : https://prove2.me/theorems/763236b8-2f60-4906-8cc8-a24693c607b5
-- title:
--   Lemma 6 — the $\psi^i$ are orthonormal
-- statement:
--   Let $h$ be even and $s\in\{\ell,r\}^{h/2}$. For $i\in\mathcal L(\mathcal T^s)$,
--   $$\|\psi^i\|_2^2=1,$$
--   and for $i\ne j$ in $\mathcal L(\mathcal T^s)$,
--   $$\langle\psi^i,\psi^j\rangle=0.$$
--
--   Orthonormality bounds the sum of the squared measurements of the noise by its squared $\ell_2$ norm.
--
--   Differences from the source:
--   - reading: Algorithm 1 (p.26) sets ψ^i_u = ±2^{−(h/2−d)/2} at every even-depth u; p.12 and App. C set ψ^i_u = 0 for i ∉ L(T^u) → the ancestor-only vector of p.12 and App. C; reason: this is the vector of the proof of Lemma 6 (App. C: "all other nodes contribute 0"); the literal loop would make ∥ψ^i∥² ≠ 1
--   - generalization: §5 assumes n is a power of 16 → every even h; reason: the proof needs only that h/2 is an integer
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Lemma 6, p.28 (PDF p.29); proof App. C, p.41 (PDF p.42)

import Mathlib
import Definitions.Def_ContinualCounting_psi

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Lemma 6 (the `ψ^i` are orthonormal).** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…),
p.28: "For i ∈ L(T^s) we have ∥ψ^i∥_2^2 = 1 and for i ≠ j with i, j ∈ L(T^s), we have ⟨ψ^i, ψ^j⟩ = 0."

**Formalization Note.** `ψ^i` is the ancestor-only vector of p.12 and App. C, see `psi`. The inner product
runs over the nodes of `T^s` at even depth `< h` and the dummy coordinate. -/
theorem lemma_6_psi_orthonormal {h : ℕ} (hh : Even h) (s : Fin (h / 2) → Bool) :
    (∀ i ∈ leavesTs h s, attackInner h s (psi h i) (psi h i) = 1) ∧
    (∀ i ∈ leavesTs h s, ∀ j ∈ leavesTs h s, i ≠ j →
      attackInner h s (psi h i) (psi h j) = 0) := by sorry

end ContinualCounting
