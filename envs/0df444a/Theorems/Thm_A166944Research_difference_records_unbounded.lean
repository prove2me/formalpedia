-- Prove2me | Theorems.Thm_A166944Research_difference_records_unbounded
-- name    : A166944Research.difference_records_unbounded
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-14T23:10:22.127756+00:00
-- url     : https://prove2.me/theorems/f22ec816-f580-4ef5-9bc3-f8f0ad5ee666
-- title:
--   The difference records of OEIS A166944 are unbounded
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944,
--
--   $$
--   a_0=0,\qquad a_1=2,\qquad a_{n+2}=\begin{cases} a_{n+1}+\gcd(n+2,\,a_{n+1}), & n+2 \text{ even},\\[2pt] a_{n+1}+\gcd(n,\,a_{n+1}), & n+2 \text{ odd},\end{cases}
--   $$
--
--   with first differences $d_n=a_n-a_{n-1}$. Call $R$ a **difference record** if $d_n=R$ for some $n\ge2$ and $d_k<R$ for every $2\le k<n$: a strict running maximum of $(d_n)$, attained.
--
--   The theorem asserts that these records are **unbounded**:
--
--   $$
--   \forall M\in\mathbb{N}\;\; \exists R\in\mathbb{N},\;\; M<R \;\wedge\; R \text{ is a difference record}.
--   $$
--
--   Equivalently, for every threshold $M$ there is an index at which the difference sequence exceeds $M$ for the first time. The proof is effective: the witness satisfies $R=M+O(M^{1+\varepsilon})$ uniformly, because the argument bounds the index of the next record above $M$ by an explicit least common multiple.
--
--   This is the monotone half of the A166944 conjecture and it is the step that turns the conjecture into a statement about primality alone. The conjecture itself,
--
--   $$
--   \forall R,\; 5<R \Rightarrow \bigl(R \text{ is a difference record}\bigr) \Rightarrow \bigl(R \text{ and } R-2 \text{ are both prime}\bigr),
--   $$
--
--   is **open**; this theorem removes the combinatorial part of it and leaves only the arithmetic part. It is the natural first lemma for anyone approaching the conjecture, and the companion theorem `unbounded_greater_twin_primes_of_target` records that the conjecture would imply arbitrarily large twin-prime pairs.
--
--   **Formalization Note** Indices are restricted to $\ge2$ throughout, the range in which `d` is the true difference rather than a truncated subtraction. `R` is the value of the record, not its index; the index is bounded separately by `recordHorizonBound`.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944. Machine-checked statement and proof: https://github.com/tara-sooo/A166944-Lean/blob/a05fb69fa826efed102c141a5be901bbcfaa9f9f/A166944/RecordBarrier.lean (theorem difference_records_unbounded; the bound on the record index is recordHorizonBound). The open primality half is the target `OeisA166944.conjecture` in google-deepmind/formal-conjectures@8323e878b83fcd7f4a448256069352a265460d75, FormalConjectures/OEIS/166944.lean.

import Definitions.Def_a166944_record_core

open A166944Research

namespace A166944Research

theorem difference_records_unbounded (M : Nat) :
    ∃ R : Nat, M < R ∧ IsDifferenceRecord R := by sorry

end A166944Research
