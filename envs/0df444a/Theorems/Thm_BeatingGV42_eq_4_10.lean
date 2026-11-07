-- Prove2me | Theorems.Thm_BeatingGV42_eq_4_10
-- name    : BeatingGV42.eq_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:15.290363+00:00
-- url     : https://prove2.me/theorems/191f806c-b395-457c-b7e5-de310df96b1a
-- title:
--   Eq. (4.10) — $|\mathcal H|=[T^{m-N+w}]\bigl(Z_F(T)(1-T)^w\bigr)$
-- statement:
--   In the setting of Claim 4.4 (a function field $F/\mathbb F_Q$ of genus $g$, distinct rational places $P_1,\dots,P_N$, $2g-2<m<N$, $S\subseteq[N]$ with $|S|=w\ge1$), the number of effective divisors of degree $m-N+w$ that vanish at every $P_i$ with $i\in S$ is
--   $$
--   |\mathcal H|=[T^{m-N+w}]\bigl(Z_F(T)(1-T)^w\bigr),
--   \tag{4.10}
--   $$
--   where $[T^r]$ is zero for $r<0$. Together with Claim 4.4 it gives eq. (4.8) and hence Lemma 4.3.
--
--   **Formalization Note** The function field $F/\mathbb F_Q$ is encoded by the platform's `AlgebraicCurve` library: a finite field `k` with $Q$ = `Nat.card k`, and $F$ with `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`; $g$ = `genusFF k F`. The places are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`. $|\mathcal H|$ is a `Nat.card` cast to $\mathbb Z$; $Z_F$ is `zeta k F` and $[T^r]$ is `coeffZ r`.
--
--   Differences from the source:
--   - encoding: F/F_Q an algebraic function field of one variable with full constant field F_Q → k a finite field with Q = Nat.card k; F with [IsCurveOver k F], [Algebra.EssFiniteType k F] and ConstantsAreBase k F (platform AlgebraicCurve library); reason: every such function field satisfies these conditions, and a field satisfying them is finitely generated of transcendence degree 1 over k (Ω_{F/k} free of rank 1, k perfect) with L(0) = k; same objects
--   - encoding: distinct rational places P_1, …, P_N, D = P_1 + ⋯ + P_N → P : Fin N → Place k F injective with (P i).deg = 1 for all i; reason: a rational place is a place of degree one (§3, p.10); same data
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Proof of Lemma 4.3, eq. (4.10), p.16 (PDF p.18), with the set H of p.15 (PDF p.17)

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_BeatingGV42_zeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

/-- **Eq. (4.10)**, proof of Lemma 4.3 (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), p.16 (PDF p.18)): for `S ⊆ [N]` with `|S| = w` and
"H = {H ∈ Div(F) : H ≥ 0, deg H = m − N + w and ν_{P_i}(H) = 0 for all i ∈ S}" (p.15),
"|H| = [T^{m−N+w}] (Z_F(T)(1 − T)^w)." (4.10)

**Formalization Note** The function field `F/F_Q` (one variable, full constant field `F_Q`) is encoded by the
platform's `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`, with `k`
any finite field and `Q = Nat.card k`; `g = genusFF k F`. The distinct rational places
`P_1, …, P_N` are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`
(`D = P_1 + ⋯ + P_N`). The section's standing choice "Fix an integer 2g − 2 < m < N" (p.13) is
kept as the hypotheses `hm`, `hmN`. `w = S.card` with `1 ≤ w` (`w ∈ [N]`). `Z_F(T)` is `zeta k F` (a power
series over `ℤ`), `[T^r]` is `coeffZ r` (zero for `r < 0`), and `|H|` is `Nat.card` of the set of such
divisors, cast to `ℤ`. -/
theorem eq_4_10 (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F] (hC : ConstantsAreBase k F)
    {N : ℕ} (P : Fin N → Place k F) (hP : Function.Injective P) (hdeg : ∀ i, (P i).deg = 1)
    (m : ℕ) (hm : 2 * (genusFF k F : ℤ) - 2 < m) (hmN : m < N)
    (S : Finset (Fin N)) (hS : 1 ≤ S.card) :
    (Nat.card {E : Divisor k F // 0 ≤ E ∧ Divisor.degree E = (m : ℤ) - N + S.card ∧
        ∀ i ∈ S, E (P i) = 0} : ℤ) =
      coeffZ ((m : ℤ) - N + S.card) (zeta k F * (1 - PowerSeries.X) ^ S.card) := by sorry

end BeatingGV42
