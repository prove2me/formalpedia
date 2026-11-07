-- Prove2me | Theorems.Thm_BeatingGV42_lemma_4_1
-- name    : BeatingGV42.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:10.58755+00:00
-- url     : https://prove2.me/theorems/06a2ccbe-ef44-46ff-a5f3-71c7b9a0d206
-- title:
--   Lemma 4.1 — alphabet restriction and expurgation: $W_q(C_1,d)\le1$ gives a $q$-ary code of distance $d$ and size $\ge\frac12|C_1|(q/Q)^N$
-- statement:
--   Let $Q$ be a prime power, $2\le q\le Q$ an integer, $C_1\subseteq\mathbb F_Q^N$ a linear code and $d\in[N+1]=\{1,\dots,N+1\}$. If $W_q(C_1,d)\le 1$, then there is a $q$-ary code $C_2\subseteq[q]^N$ of length $N$ with minimum distance $d(C_2)\ge d$ and
--   $$
--   |C_2|\ \ge\ \frac12\,|C_1|\left(\frac qQ\right)^N .
--   \tag{4.3}
--   $$
--   This is the step that converts a code over the large alphabet $\mathbb F_Q$ with few low-weight codewords into a code over the alphabet of size $q$ with a larger guaranteed distance; it is applied to the mother codes in the proof of Proposition 4.9.
--
--   **Formalization Note** $\mathbb F_Q$ is any finite field `k` with $Q$ = `Nat.card k` (automatically a prime power); $C_1$ is a `Submodule k (Fin N → k)`, $C_2$ a `Finset (Fin N → Fin q)`, the distance condition is `MinDistAtLeast` over distinct codewords, and (4.3) is a real inequality.
--
--   Differences from the source:
--   - encoding: a linear code C_1 ⊆ F_Q^N, Q a prime power → C₁ : Submodule k (Fin N → k) for a finite field k, Q = Nat.card k; reason: F_Q is a finite field of size Q; same codes
--   - encoding: a q-ary code C_2 of length N → C₂ : Finset (Fin N → Fin q); reason: any alphabet of size q is in bijection with Fin q; the proof itself maps into [q]^N
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Lemma 4.1, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_BeatingGV42_MinDistAtLeast
import Definitions.Def_BeatingGV42_truncWE

set_option autoImplicit false

namespace BeatingGV42

/-- **Lemma 4.1** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.1, p.12 (PDF p.14)): "Let C_1 ⊆ F^N_Q be a linear code and let
d ∈ [N + 1]. If W_q(C_1, d) ≤ 1, then there exists a q-ary code C_2 of length N and minimum
distance d(C_2) ≥ d satisfying |C_2| ≥ (1/2) · |C_1| · (q/Q)^N." (4.3)
Standing assumptions of §4 (p.11): Q is a prime power and `2 ≤ q ≤ Q` is an integer.

**Formalization Note** `F_Q` is any finite field `k` and `Q = Nat.card k` (automatically a prime
power). `d ∈ [N + 1]` is `1 ≤ d ≤ N + 1`. A `q`-ary code of length `N` is a
`Finset (Fin N → Fin q)`; "minimum distance ≥ d" is `MinDistAtLeast C₂ d` (distinct codewords). The
bound (4.3) is a real inequality. -/
theorem lemma_4_1 {k : Type*} [Field k] [Finite k] {N : ℕ} (q : ℕ) (hq : 2 ≤ q)
    (hqQ : q ≤ Nat.card k) (C₁ : Submodule k (Fin N → k)) (d : ℕ) (hd : 1 ≤ d)
    (hdN : d ≤ N + 1) (hW : truncWE q C₁ d ≤ 1) :
    ∃ C₂ : Finset (Fin N → Fin q), MinDistAtLeast C₂ d ∧
      (1 / 2 : ℝ) * (Nat.card C₁ : ℝ) * ((q : ℝ) / (Nat.card k : ℝ)) ^ N ≤ (C₂.card : ℝ) := by sorry

end BeatingGV42
