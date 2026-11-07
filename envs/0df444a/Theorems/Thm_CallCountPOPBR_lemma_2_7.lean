-- Prove2me | Theorems.Thm_CallCountPOPBR_lemma_2_7
-- name    : CallCountPOPBR.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:46.053521+00:00
-- url     : https://prove2.me/theorems/e228214d-a6c7-4bf0-87fb-e85bdbf21f9d
-- title:
--   Lemma 2.7 — additive form and visibility
-- statement:
--   Let $(N,d,p,\mathrm{Obs})$ be a well-formed instance, $(a_r,b_r)_{r<p}$ an admissible rule and $C$ a completion, and write $E_n=(C_n+1)/2$. Then:
--
--   1. every $C_n$ ($n\le N$) is odd;
--   2. $E_n=1$ for $0\le n<d$;
--   3. for $d\le n\le N$,
--   $$
--   E_n=E_{n-a_{n\bmod p}}+E_{n-b_{n\bmod p}};\qquad(4)
--   $$
--   4. if $p=N+1$, distinct indices $n,n'\le N$ have distinct phases $n\bmod p\ne n'\bmod p$;
--   5. if $p=N+1$, every choice of pairs $(a_n,b_n)$ for the indices $n\le N$ is realised by a rule read at $n\bmod p$ (the pairs can be chosen independently);
--   6. if $p=N+1$ and $N\le 2d-1$, then for every $n\in[d,N]$ the indices $n-1,\dots,n-d$ reached by the offsets $1,\dots,d$ are exactly $n-d,\dots,n-1$, and $n-d\le d-1$, so at least one base index is visible (all base indices have $E=1$ by item 2).
--
--   The lemma turns POPBR into an addition-sequence completion problem in which, for the hard instances, every recursive index sees the base value $1$ and all earlier recursive values.
--
--   Differences from the source:
--   - encoding: E_n = (C_n + 1)/2 → natural-number division (C n + 1) / 2; reason: exact because every C_n is odd (clause 1)
--   - reading: the pairs (a_n, b_n), d ≤ n ≤ N, can be chosen independently → distinct phases (clause 4) and every family of pairs indexed by n ≤ N is rule' (n % p) for some rule' (clause 5); reason: the sentence's content made explicit; clause 5 quantifies over all n ≤ N, which contains d ≤ n ≤ N
--   - reading: the offsets 1, …, d refer exactly to the base indices n − d, …, d − 1 (at least one, all with E = 1) and to all recursive indices d, …, n − 1 → {n − o : 1 ≤ o ≤ d} = [n − d, n − 1] and n − d < d; E = 1 on base indices is clause 2; reason: the window [n − d, n − 1] is the union of the base indices n − d, …, d − 1 and the recursive indices d, …, n − 1
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Lemma 2.7, Eq. (4), p.5

import Definitions.Def_CallCountPOPBR_Instance_IsValid
import Definitions.Def_CallCountPOPBR_IsAdmissibleRule
import Definitions.Def_CallCountPOPBR_IsCompletion
import Definitions.Def_CallCountPOPBR_Eval

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Lemma 2.7 (Additive form and visibility).** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Lemma 2.7, p.5: "Let (C_n) satisfy
the conditions of Definition 2.1. Then every C_n is odd, E_n = 1 for 0 ≤ n < d, and
E_n = E_{n − a_{n mod p}} + E_{n − b_{n mod p}} (d ≤ n ≤ N). (4) If p = N + 1, distinct
indices have distinct phases, so the pairs (a_n, b_n), d ≤ n ≤ N, can be chosen independently.
If moreover 2d − 1 ≥ N, then for every n ∈ [d, N] the offsets 1, …, d refer exactly to the base
indices n − d, …, d − 1 (at least one, all with E = 1) and to all recursive indices d, …, n − 1."

Clauses: (i) oddness; (ii) `E_n = 1` on base indices; (iii) Eq. (4); (iv) distinct phases when
`p = N + 1`, and (v) every family of pairs indexed by `n ≤ N` is a rule read at `n mod p`
("can be chosen independently"); (vi) when also `N ≤ 2d − 1`, for `d ≤ n ≤ N` the indices
`n − o`, `1 ≤ o ≤ d`, are exactly `n − d, …, n − 1`, and `n − d ≤ d − 1` (at least one base
index; their `E`-values are 1 by (ii)). -/
theorem lemma_2_7 (I : Instance) (rule : ℕ → ℕ × ℕ) (C : ℕ → ℕ)
    (hI : I.IsValid) (hrule : IsAdmissibleRule I.d I.p rule) (hC : IsCompletion I rule C) :
    (∀ n, n ≤ I.N → Odd (C n)) ∧
    (∀ n, n < I.d → Eval C n = 1) ∧
    (∀ n, I.d ≤ n → n ≤ I.N →
      Eval C n = Eval C (n - (rule (n % I.p)).1) + Eval C (n - (rule (n % I.p)).2)) ∧
    (I.p = I.N + 1 → ∀ n n', n ≤ I.N → n' ≤ I.N → n % I.p = n' % I.p → n = n') ∧
    (I.p = I.N + 1 → ∀ pairs : ℕ → ℕ × ℕ, ∃ rule' : ℕ → ℕ × ℕ,
      ∀ n, n ≤ I.N → rule' (n % I.p) = pairs n) ∧
    (I.p = I.N + 1 → I.N ≤ 2 * I.d - 1 → ∀ n, I.d ≤ n → n ≤ I.N →
      n - I.d < I.d ∧ (Finset.Icc 1 I.d).image (fun o => n - o) = Finset.Ico (n - I.d) n) := by sorry

end CallCountPOPBR
