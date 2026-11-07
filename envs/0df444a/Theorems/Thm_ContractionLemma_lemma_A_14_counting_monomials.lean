-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_14_counting_monomials
-- name    : ContractionLemma.lemma_A_14_counting_monomials
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:33.617006+00:00
-- url     : https://prove2.me/theorems/d1a08754-4865-472f-98eb-cfcc608991bf
-- title:
--   Lemma A.14 — counting monomials
-- statement:
--   Suppose every mode $\xi$ has an integer weight $w_\xi\ge 1$, and at most $B$ modes have any given weight. Let $p'\ge 1$. Then the number of exponent vectors $\beta=(\beta_\xi)_\xi$, with nonnegative integer entries and total weight $\sum_\xi w_\xi\beta_\xi<p'$, is at most
--
--   $$
--   \exp\big(3\sqrt{Bp'}\big).
--   $$
--
--   This bounds the branching of the recursion at an easy point.
--
--   **Formalization Note** Exponent vectors are finitely supported. The conclusion says the set is finite and bounds its cardinality.
--
--   Differences from the source:
--   - generalization: the modes of a call, a finite set → an arbitrary type of modes; reason: the lemma does not say finite; a finite mode set is a special case
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.14, p.72; proof p.93

import Mathlib

set_option autoImplicit false

namespace ContractionLemma

/-- **Lemma A.14 (Counting monomials)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.72 (PDF p.75); proof p.93.

Suppose every mode `ξ` has an integer weight `w_ξ ≥ 1`, and at most `B` modes have any given
weight. Let `p′ ≥ 1`. Then the number of exponent vectors `β = (β_ξ)_ξ` with nonnegative integer
entries and total weight `∑_ξ w_ξ β_ξ < p′` is at most `exp(3√(B p′))`.

**Formalization Note.** The modes form an arbitrary type `ι` (finite or not); exponent vectors
are finitely supported (`ι →₀ ℕ`). The conclusion says the set of such vectors is finite and
its cardinality is at most `exp(3√(B p′))`. -/
theorem lemma_A_14_counting_monomials {ι : Type*} (w : ι → ℕ) (hw : ∀ ξ, 1 ≤ w ξ) (B : ℕ)
    (hB : ∀ k : ℕ, {ξ | w ξ = k}.encard ≤ B) (p' : ℕ) (hp' : 1 ≤ p') :
    {β : ι →₀ ℕ | (β.sum fun ξ n => w ξ * n) < p'}.Finite ∧
      (({β : ι →₀ ℕ | (β.sum fun ξ n => w ξ * n) < p'}.ncard : ℕ) : ℝ) ≤
        Real.exp (3 * Real.sqrt ((B : ℝ) * p')) := by sorry

end ContractionLemma
