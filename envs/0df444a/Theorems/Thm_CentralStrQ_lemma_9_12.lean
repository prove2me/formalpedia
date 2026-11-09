-- Prove2me | Theorems.Thm_CentralStrQ_lemma_9_12
-- name    : CentralStrQ.lemma_9_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:23:03.919307+00:00
-- url     : https://prove2.me/theorems/3acfebd0-fb35-4113-ad35-d2de4f60112a
-- title:
--   Lemma 9.12 — owned positions and profile values at synchronizing positions
-- statement:
--   Let $T\in\Sigma^N$, $\tau\in[1\,.\,.\,\lfloor N/3\rfloor]$, and let $S$ be a nonempty τ-synchronizing set of $T$, with $k$, $(s_i)$, $J_i$ and the labels $W$ as in Definition 9.11. Let $C\ge2\tau$ and let $A$ be the $C$-capped LCE sequence of $S$. Then:
--
--   1. the sets $J_i$ are pairwise disjoint, and
--   $$
--   \bigcup_{i=1}^{k}\bigl(J_i\cap[1\,.\,.\,N-3\tau+2]\bigr)=[1\,.\,.\,N-3\tau+2]\setminus R(\tau,T);
--   $$
--   2. for $i\in[1\,.\,.\,k]$ and $j\in J_i$, with $\delta=s_i-j$, $p=2\tau+\delta$ and $D=T[j\,.\,.\,s_i+2\tau)$: if $j=\mathrm{SA}_T[\mathrm{RangeBeg}(D,T)+1]$, then $\mathrm{profile}_{A,W}(i)[p]=0$ and $\mathrm{PLCP}_T[j]<p$; otherwise
--   $$
--   \mathrm{profile}_{A,W}(i)[p]=\min\{C,\ \mathrm{PLCP}_T[j]-\delta\}\ \ge\ 2\tau .
--   $$
--
--   So the LCP profiles of the labels give the (capped) PLCP values of all nonperiodic positions.
--
--   Differences from the source:
--   - encoding: min{C, PLCP_T[j] − δ} → computed in ℤ; reason: avoids natural subtraction
--   - encoding: τ ∈ [1..⌊N/3⌋] → 1 ≤ τ and 3τ ≤ N; reason: same condition
--   - encoding: strings in Σⁿ with 1-based positions → lists over a linearly ordered type, 1-based access; reason: a Lean convention; same instances
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Lemma 9.12, p.166 (PDF p.167); Definition 9.11, p.166 (PDF p.167)

import Mathlib
import Definitions.Def_CentralStrQ_Strings
import Definitions.Def_CentralStrQ_LCPProfile
import Definitions.Def_CentralStrQ_SyncSet

set_option autoImplicit false

namespace CentralStrQ

/-- Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*, STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Lemma 9.12, p.166 (PDF p.167): "Let T, τ, S, k, (s_i)_{i∈[1..k]}, J_i, and W be as in
Definition 9.11. Let C ∈ ℤ≥2τ, and let A be the C-capped LCE sequence of S. The following claims
hold: 1. The sets J_i are pairwise disjoint, and the union of the sets J_i ∩ [1..N − 3τ + 2], for
i ∈ [1..k], is [1..N − 3τ + 2] \ R(τ, T) (Definition 3.38). 2. Let i ∈ [1..k] and j ∈ J_i, and denote
δ = s_i − j, p = 2τ + δ, and D = T[j..s_i + 2τ). If j = SA_T[RangeBeg(D, T) + 1], then
profile_{A,W}(i)[p] = 0 and PLCP_T[j] < p. Otherwise, profile_{A,W}(i)[p] = min{C, PLCP_T[j] − δ} ≥ 2τ."

Definition 9.11 (p.166): `T ∈ Σ^N`, `τ ∈ [1..⌊N/3⌋]`, `S` a nonempty τ-synchronizing set,
`k = |S|`, `(s_i) = LexSorted(S, T)`, `J_i = [a_i..s_i]`, `W[i]` the reverse of `T[a_i..s_i+2τ)`.

**Formalization Note.** `τ ∈ [1..⌊N/3⌋]` is `1 ≤ τ ∧ 3τ ≤ N`. The value `min{C, PLCP_T[j] − δ}`
is computed in `ℤ`. The labels, owned sets and capped LCE sequence are those of
`Def_CentralStrQ_SyncSet`. -/
theorem lemma_9_12 {α : Type} [LinearOrder α] (T : List α) (τ : ℕ) (S : Finset ℕ) (C : ℕ)
    (hτ : 1 ≤ τ) (hτN : 3 * τ ≤ T.length) (hS : S.Nonempty) (hsync : IsSyncSet τ T S)
    (hC : 2 * τ ≤ C) :
    ((∀ i ∈ Finset.Icc 1 S.card, ∀ i' ∈ Finset.Icc 1 S.card, i ≠ i' →
        Disjoint (owned T τ S i) (owned T τ S i')) ∧
      (Finset.Icc 1 S.card).biUnion (fun i => owned T τ S i ∩ Finset.Icc 1 (T.length + 2 - 3 * τ)) =
        Finset.Icc 1 (T.length + 2 - 3 * τ) \ periodicPositions τ T) ∧
    ∀ i ∈ Finset.Icc 1 S.card, ∀ j ∈ owned T τ S i,
      (j = SA T (rangeBeg (factor T j (sAt T S i + 2 * τ)) T + 1) →
        profile (cappedLCE T S C) (labels T τ S) i (2 * τ + (sAt T S i - j)) = 0 ∧
        PLCP T j < 2 * τ + (sAt T S i - j)) ∧
      (j ≠ SA T (rangeBeg (factor T j (sAt T S i + 2 * τ)) T + 1) →
        ((profile (cappedLCE T S C) (labels T τ S) i (2 * τ + (sAt T S i - j)) : ℕ) : ℤ) =
          min (C : ℤ) ((PLCP T j : ℤ) - ((sAt T S i - j : ℕ) : ℤ)) ∧
        2 * τ ≤ profile (cappedLCE T S C) (labels T τ S) i (2 * τ + (sAt T S i - j))) := by sorry

end CentralStrQ
