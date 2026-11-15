-- Prove2me | Theorems.Thm_A166944Research_record_index_iff_canonical_returns
-- name    : A166944Research.record_index_iff_canonical_returns
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-14T23:13:12.070227+00:00
-- url     : https://prove2.me/theorems/bfc460ca-8cc4-496a-a778-b53c1219bd68
-- title:
--   The A166944 record-index law is equivalent to a canonical return at $B=2$
-- statement:
--   Let $a$ be the Rowland-type recursion of OEIS A166944 with first differences $d_n=a_n-a_{n-1}$, and let
--
--   $$
--   B_n=a_n-(2n-2)
--   $$
--
--   be the offset coordinate measuring how far $a_n$ has advanced past the linear benchmark $2n-2$.
--
--   The **record-index law** says that a difference record of value $R>5$ can only be attained at the index $R+2$:
--
--   $$
--   (\mathrm{I})\quad \forall R,n,\;\; 5<R \;\wedge\; 2\le n \;\wedge\; d_n=R \;\wedge\; (\forall j,\,2\le j<n \Rightarrow d_j<R) \;\Longrightarrow\; n=R+2.
--   $$
--
--   The **canonical return** statement says that from a canonical record — a value $M>5$ attained at index exactly $M+2$, with $M$ an attained maximum on the prefix up to $k$ and a strictly larger increment at $k+1$ — the sequence must come back down to the offset $B=2$ before that larger increment is taken:
--
--   $$
--   (\mathrm{II})\quad \forall M,k,\;\; 5<M \;\wedge\; M+2\le k \;\wedge\; d_{M+2}=M \;\wedge\; \text{$M$ attained max on } [2,k] \;\wedge\; M<d_{k+1} \;
--   \Longrightarrow\; \exists m,\; M+2\le m<k+1 \;\wedge\; B_m=2.
--   $$
--
--   The theorem is the **equivalence** $(\mathrm{I})\leftrightarrow(\mathrm{II})$: the index law for all records holds if and only if no canonical replay overshoots its horizon before returning to $B=2$. This converts a statement about the global record sequence into a statement about a single finite object — one capped replay from a canonical record — and is therefore the pivot on which the remaining obstruction rests.
--
--   The status of the A166944 conjecture is **open**, and so is $(\mathrm{I})$; what is proved here is only the equivalence, which is a genuine advance because $(\mathrm{II})$ is a self-contained statement about one trajectory segment that can be attacked, searched for counterexamples, and decomposed. Neither side is asserted to be true.
--
--   **Formalization Note** `B` is truncated subtraction on `Nat`, and `IsAttainedPreviousMaximum M k` is the conjunction “$d_j\le M$ for $2\le j\le k$” and “$d_r=M$ for some $2\le r\le k$”, so the maximum is required to be attained and not merely an upper bound. Both sides of the equivalence use the same binder style, with implicit `R, n` on the left and implicit `M, k` on the right.
-- source:
--   OEIS Foundation, sequence A166944, https://oeis.org/A166944. Machine-checked equivalence: https://github.com/tara-sooo/A166944-Lean/blob/a05fb69fa826efed102c141a5be901bbcfaa9f9f/A166944/CanonicalRecord.lean (theorem record_index_iff_canonical_returns). Supporting definitions: https://github.com/tara-sooo/A166944-Lean/blob/a05fb69fa826efed102c141a5be901bbcfaa9f9f/A166944/ResearchDefs.lean. Index law target `OeisA166944.conjecture` at google-deepmind/formal-conjectures@8323e878b83fcd7f4a448256069352a265460d75, FormalConjectures/OEIS/166944.lean.

import Definitions.Def_a166944_canonical

open A166944Research

namespace A166944Research

theorem record_index_iff_canonical_returns :
    (∀ {R n : Nat}, 5 < R → 2 ≤ n → d n = R →
      (∀ j : Nat, 2 ≤ j → j < n → d j < R) → n = R + 2) ↔
    (∀ {M k : Nat}, 5 < M → M + 2 ≤ k → d (M + 2) = M →
      IsAttainedPreviousMaximum M k → M < d (k + 1) →
      ∃ m : Nat, M + 2 ≤ m ∧ m < k + 1 ∧ B m = 2) := by sorry

end A166944Research
