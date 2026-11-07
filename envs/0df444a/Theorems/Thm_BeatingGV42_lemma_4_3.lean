-- Prove2me | Theorems.Thm_BeatingGV42_lemma_4_3
-- name    : BeatingGV42.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:27.918104+00:00
-- url     : https://prove2.me/theorems/4a345e0a-9ffc-4a6e-935f-3ef4111d5c52
-- title:
--   Lemma 4.3 — the average weight distribution of the codes $C_\gamma$ via the zeta function
-- statement:
--   Let $F/\mathbb F_Q$ be a function field of genus $g$ with class number $h_F$, $P_1,\dots,P_N$ distinct rational places, $D=P_1+\dots+P_N$, $2g-2<m<N$, and for each $\gamma\in\mathcal C^m_F$ let $G_\gamma$ be a representative with $\operatorname{supp}(G_\gamma)\cap\operatorname{supp}(D)=\emptyset$ and $C_\gamma=C_L(D,G_\gamma)$. Then for each $w\in[N]$,
--   $$
--   \mathbb E_\gamma\bigl[A_w(C_\gamma)\bigr]=\frac{Q-1}{h_F}\binom Nw\,[T^{m-N+w}]\bigl(Z_F(T)(1-T)^w\bigr),
--   \tag{4.7}
--   $$
--   the expectation being over $\gamma\in\mathcal C^m_F$ uniformly at random, i.e. $\mathbb E_\gamma=\frac1{h_F}\sum_{\gamma\in\mathcal C^m_F}$.
--
--   This coefficient form of Duursma's average weight distribution is what makes the number of low-weight codewords computable from the zeta function.
--
--   **Formalization Note** The function field $F/\mathbb F_Q$ is encoded by the platform's `AlgebraicCurve` library: a finite field `k` with $Q$ = `Nat.card k`, and $F$ with `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`; $g$ = `genusFF k F`. The places are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`. The identity is stated for every choice of representatives; $A_w$ is `weightDist`, $h_F$ is `classNumber k F`, the sum is a `finsum` over the finite set $\mathcal C^m_F$.
--
--   Differences from the source:
--   - encoding: F/F_Q an algebraic function field of one variable with full constant field F_Q → k a finite field with Q = Nat.card k; F with [IsCurveOver k F], [Algebra.EssFiniteType k F] and ConstantsAreBase k F (platform AlgebraicCurve library); reason: every such function field satisfies these conditions, and a field satisfying them is finitely generated of transcendence degree 1 over k (Ω_{F/k} free of rank 1, k perfect) with L(0) = k; same objects
--   - encoding: distinct rational places P_1, …, P_N, D = P_1 + ⋯ + P_N → P : Fin N → Place k F injective with (P i).deg = 1 for all i; reason: a rational place is a place of degree one (§3, p.10); same data
--   - encoding: for each class γ ∈ C^m_F fix a representative G_γ as in Claim 4.2 → any G : Pic k F → Divisor k F with [G γ] = γ and ∀ i, G γ (P i) = 0 for every γ ∈ C^m_F; reason: the statement holds for each choice of representatives, which is what fixing an arbitrary one means
--   - encoding: E_γ, expectation over γ ∈ C^m_F chosen uniformly at random → (∑ᶠ γ ∈ degClasses k F m, ·) / classNumber k F; reason: the first display of the proof of Lemma 4.3 (p.14) writes E_γ as (1/h_F)·Σ_{γ∈C^m_F}, using |C^m_F| = h_F (p.11, p.13)
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Lemma 4.3, p.14 (PDF p.16)

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

/-- **Lemma 4.3** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.2, p.14 (PDF p.16)): "For each w ∈ [N] we have
E_γ [A_w(C_γ)] = ((Q − 1)/h_F) (N choose w) [T^{m−N+w}] (Z_F(T)(1 − T)^w), (4.7)
where the expectation is taken over γ ∈ C^m_F chosen uniformly at random." Here
`C_γ = C_L(D, G_γ)` with `G_γ` the representative fixed after Claim 4.2.

**Formalization Note** The function field `F/F_Q` (one variable, full constant field `F_Q`) is encoded by the
platform's `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`, with `k`
any finite field and `Q = Nat.card k`; `g = genusFF k F`. The distinct rational places
`P_1, …, P_N` are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`
(`D = P_1 + ⋯ + P_N`). The section's standing choice "Fix an integer 2g − 2 < m < N" (p.13) is
kept as the hypotheses `hm`, `hmN`. "For each class γ ∈ C^m_F fix a representative G_γ as in Claim 4.2":
the identity is stated for every choice `G : Pic k F → Divisor k F` with `[G γ] = γ` and
`supp(G γ) ∩ supp(D) = ∅` for `γ ∈ C^m_F`. `E_γ` is `(1/h_F) Σ_{γ ∈ C^m_F}`, as in the first display of
the proof (the paper recalls `|C^m_F| = h_F`), with `h_F = classNumber k F = Nat.card (Pic0 k F)` and
the sum a `finsum` over the finite set `C^m_F`. `A_w` is `weightDist`, `Z_F` is `zeta k F`, `[T^r]` is
`coeffZ`, and `Q = Nat.card k`. -/
theorem lemma_4_3 (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F] (hC : ConstantsAreBase k F)
    {N : ℕ} (P : Fin N → Place k F) (hP : Function.Injective P) (hdeg : ∀ i, (P i).deg = 1)
    (m : ℕ) (hm : 2 * (genusFF k F : ℤ) - 2 < m) (hmN : m < N)
    (G : Pic k F → Divisor k F)
    (hG : ∀ γ ∈ degClasses k F m, (QuotientAddGroup.mk (G γ) : Pic k F) = γ ∧ ∀ i, G γ (P i) = 0)
    (w : ℕ) (hw : 1 ≤ w) (hwN : w ≤ N) :
    (∑ᶠ γ ∈ degClasses k F m, (weightDist (goppaCode P (G γ)) w : ℝ)) / (classNumber k F : ℝ) =
      ((Nat.card k : ℝ) - 1) / (classNumber k F : ℝ) * (N.choose w : ℝ) *
        (coeffZ ((m : ℤ) - N + w) (zeta k F * (1 - PowerSeries.X) ^ w) : ℝ) := by sorry

end BeatingGV42
