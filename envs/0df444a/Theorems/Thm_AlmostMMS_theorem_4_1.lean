-- Prove2me | Theorems.Thm_AlmostMMS_theorem_4_1
-- name    : AlmostMMS.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:40.706099+00:00
-- url     : https://prove2.me/theorems/3325feab-f8ba-485b-a93a-de61dfad22fd
-- title:
--   Theorem 4.1 — partial selection
-- statement:
--   Let $M=E+S$ be any partition of the items, and let $V\subseteq N$ with $|V|\ge d$. There are $A\subseteq V$ and $j_i\in[d]$, $i\in A$, such that, for $\pi_i=\pi_{i,j_i}$:
--
--   1. $\Delta(\pi_i)=0$ and $\pi^S_{i,j_i}=\emptyset$;
--   2. the $\pi_i$ are simultaneously satisfied by distinct items of $E$, and for every $0\le\ell\le m$,
--   $$
--   \sum_{i\in A}P_i(\pi_i,\ell)\le\frac1{|V|}\sum_{i\in V}\sum_{j=1}^dP_i(\pi^E_{i,j},\ell);
--   $$
--   3. with $\rho_A=8+16q\log n$,
--   $$
--   |A|\ge d-|S|-\frac{q(q-1)}{|V|}\sum_{i\in V}T_i-\rho_A.
--   $$
--   When $|S|$ and the average tail are small this selects almost all of the $d$ agents, with no deficit and without touching $S$.
--
--   Differences from the source:
--   - generalization: standing d ≤ (1 − ε)n → d < n; reason: the proof's count X* ≤ (d + 1)n ≤ n² uses only d < n, which the standing bound implies
--   - encoding: the set S and E := M − S → a set S and E = Sᶜ; reason: the same partitions
--   - encoding: choices j_i for i ∈ A → a total function j : Fin n → Fin d read only on A; reason: values off A play no role
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 4.1, p.28

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_IsPartialSelection

namespace AlmostMMS

open Finset

/-- **Theorem 4.1 (Partial selection), p.28.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): let `M = E + S` be any partition of the items and
`V ⊆ N` with `|V| ≥ d`. There are `A ⊆ V` and profile choices `j_i ∈ [d]`, `i ∈ A`, with the three bullets
of the theorem; see `IsPartialSelection`.

**Formalization Note.** `E = Sᶜ`. The binder `d < n` is what the proof uses of the standing
`d ≤ (1 - ε) n`, through the count `X* ≤ (d + 1) n ≤ n²`. The printed sentence after the third bullet ("I.e,
when …") is commentary, not a clause. -/
theorem theorem_4_1 {n m d q : ℕ} (hq : 3 ≤ q) (hd : 1 ≤ d) (hdn : d < n)
    (J : OrderedInstance n m d) (S : Finset (Fin m)) (V : Finset (Fin n)) (hV : d ≤ V.card) :
    ∃ (A : Finset (Fin n)) (j : Fin n → Fin d), IsPartialSelection J q S V A j := by sorry

end AlmostMMS
