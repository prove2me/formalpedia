-- Prove2me | Theorems.Thm_BeatingGV42_corollary_4_5
-- name    : BeatingGV42.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:37.81982+00:00
-- url     : https://prove2.me/theorems/e7d06677-fecb-4e8e-9242-a976e5e43132
-- title:
--   Corollary 4.5 — $\mathbb E_\gamma[A_w(C_\gamma)]\le\frac{Q-1}{h_F}\binom Nw Z_F(t)\,t^{-(m-N+w)}(1-t)^w$
-- statement:
--   In the setting of Lemma 4.3, for every $w\in[N]$ and every $0<t<1/Q$,
--   $$
--   \mathbb E_\gamma\bigl[A_w(C_\gamma)\bigr]\ \le\ \frac{Q-1}{h_F}\binom Nw\cdot Z_F(t)\cdot t^{-(m-N+w)}(1-t)^w .
--   $$
--   This replaces the exact coefficient of Lemma 4.3 by a quantity whose growth along optimal sequences Lemma 4.8 controls; it is eq. (4.19) in the proof of Proposition 4.9.
--
--   **Formalization Note** The function field $F/\mathbb F_Q$ is encoded by the platform's `AlgebraicCurve` library: a finite field `k` with $Q$ = `Nat.card k`, and $F$ with `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`; $g$ = `genusFF k F`. The places are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`. $Z_F(t)$ is `zetaAt k F t` (a `tsum`, convergent on $0<t<1/Q$) and $t^{-(m-N+w)}$ is an integer power, since $m-N+w$ may be negative.
--
--   Differences from the source:
--   - encoding: F/F_Q an algebraic function field of one variable with full constant field F_Q → k a finite field with Q = Nat.card k; F with [IsCurveOver k F], [Algebra.EssFiniteType k F] and ConstantsAreBase k F (platform AlgebraicCurve library); reason: every such function field satisfies these conditions, and a field satisfying them is finitely generated of transcendence degree 1 over k (Ω_{F/k} free of rank 1, k perfect) with L(0) = k; same objects
--   - encoding: distinct rational places P_1, …, P_N, D = P_1 + ⋯ + P_N → P : Fin N → Place k F injective with (P i).deg = 1 for all i; reason: a rational place is a place of degree one (§3, p.10); same data
--   - encoding: for each class γ ∈ C^m_F fix a representative G_γ as in Claim 4.2 → any G : Pic k F → Divisor k F with [G γ] = γ and ∀ i, G γ (P i) = 0 for every γ ∈ C^m_F; reason: the statement holds for each choice of representatives, which is what fixing an arbitrary one means
--   - encoding: E_γ, expectation over γ ∈ C^m_F chosen uniformly at random → (∑ᶠ γ ∈ degClasses k F m, ·) / classNumber k F; reason: the first display of the proof of Lemma 4.3 (p.14) writes E_γ as (1/h_F)·Σ_{γ∈C^m_F}, using |C^m_F| = h_F (p.11, p.13)
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Corollary 4.5, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_BeatingGV42_degClasses
import Definitions.Def_BeatingGV42_classNumber
import Definitions.Def_BeatingGV42_goppaCode
import Definitions.Def_BeatingGV42_truncWE
import Definitions.Def_BeatingGV42_zeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

/-- **Corollary 4.5** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.2, p.16 (PDF p.18)): "For every w ∈ [N] and 0 < t < 1/Q it holds that
E_γ [A_w(C_γ)] ≤ ((Q − 1)/h_F) (N choose w) · Z_F(t) · t^{−(m−N+w)}(1 − t)^w."

**Formalization Note** Same setting as Lemma 4.3 (`BeatingGV42.lemma_4_3`): The function field `F/F_Q` (one variable, full constant field `F_Q`) is encoded by the
platform's `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`, with `k`
any finite field and `Q = Nat.card k`; `g = genusFF k F`. The distinct rational places
`P_1, …, P_N` are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`
(`D = P_1 + ⋯ + P_N`). The section's standing choice "Fix an integer 2g − 2 < m < N" (p.13) is
kept as the hypotheses `hm`, `hmN`. The representatives
are any `G` with `[G γ] = γ` and `supp(G γ) ∩ supp(D) = ∅` on `C^m_F`; `E_γ = (1/h_F) Σ_{γ ∈ C^m_F}`.
`Z_F(t)` is `zetaAt k F t` (a `tsum`, convergent for `0 < t < 1/Q`), and `t^{−(m−N+w)}` is an integer
power (`zpow`), since `m − N + w` may be negative. -/
theorem corollary_4_5 (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F] (hC : ConstantsAreBase k F)
    {N : ℕ} (P : Fin N → Place k F) (hP : Function.Injective P) (hdeg : ∀ i, (P i).deg = 1)
    (m : ℕ) (hm : 2 * (genusFF k F : ℤ) - 2 < m) (hmN : m < N)
    (G : Pic k F → Divisor k F)
    (hG : ∀ γ ∈ degClasses k F m, (QuotientAddGroup.mk (G γ) : Pic k F) = γ ∧ ∀ i, G γ (P i) = 0)
    (w : ℕ) (hw : 1 ≤ w) (hwN : w ≤ N) (t : ℝ) (ht : 0 < t) (ht' : t < 1 / (Nat.card k : ℝ)) :
    (∑ᶠ γ ∈ degClasses k F m, (weightDist (goppaCode P (G γ)) w : ℝ)) / (classNumber k F : ℝ) ≤
      ((Nat.card k : ℝ) - 1) / (classNumber k F : ℝ) * (N.choose w : ℝ) * zetaAt k F t *
        t ^ (-((m : ℤ) - N + w)) * (1 - t) ^ w := by sorry

end BeatingGV42
