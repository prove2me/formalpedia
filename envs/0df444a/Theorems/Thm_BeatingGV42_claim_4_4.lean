-- Prove2me | Theorems.Thm_BeatingGV42_claim_4_4
-- name    : BeatingGV42.claim_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:59.040646+00:00
-- url     : https://prove2.me/theorems/852016f2-34fd-4092-9f07-c080a9871ef3
-- title:
--   Claim 4.4 — the map $\Phi(f,\gamma)=(f)+G_\gamma-\sum_{i\notin S}P_i$ is $(Q-1)$-to-one onto $\mathcal H$
-- statement:
--   Let $F/\mathbb F_Q$ be a function field of genus $g$, $P_1,\dots,P_N$ distinct rational places, $D=P_1+\dots+P_N$, $2g-2<m<N$, and for each $\gamma\in\mathcal C^m_F$ let $G_\gamma$ be a representative with $\operatorname{supp}(G_\gamma)\cap\operatorname{supp}(D)=\emptyset$. Fix $S\subseteq[N]$ with $|S|=w\ge 1$. Let
--   $$
--   U=\{(f,\gamma):\gamma\in\mathcal C^m_F,\ f\in\mathcal L(G_\gamma),\ f(P_i)\ne0\iff i\in S\},
--   $$
--   the disjoint union of the sets $F_\gamma$ of functions whose codeword has its nonzero symbols exactly at $S$, and
--   $$
--   \mathcal H=\{H\in\operatorname{Div}(F):H\ge0,\ \deg H=m-N+w,\ \nu_{P_i}(H)=0\text{ for all }i\in S\}.
--   $$
--   Then the map $\Phi:U\to\mathcal H$, $\Phi(f,\gamma)=(f)+G_\gamma-\sum_{i\in[N]\setminus S}P_i$,
--
--   1. is well defined: $\Phi(f,\gamma)\in\mathcal H$ for every $(f,\gamma)\in U$, and
--   2. is $(Q-1)$-to-one: every $H\in\mathcal H$ has exactly $Q-1$ preimages in $U$.
--
--   Consequently $\sum_\gamma|W_S(C_\gamma)|=(Q-1)|\mathcal H|$, the core count in Lemma 4.3.
--
--   **Formalization Note** The function field $F/\mathbb F_Q$ is encoded by the platform's `AlgebraicCurve` library: a finite field `k` with $Q$ = `Nat.card k`, and $F$ with `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`; $g$ = `genusFF k F`. The places are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`. The representatives are any `G : Pic k F → Divisor k F` with $[G\gamma]=\gamma$ and `∀ i, G γ (P i) = 0` on $\mathcal C^m_F$; $f(P)$ is `Place.evalAt`, $(f)$ is `divOf f`, $P_i$ as a divisor is `Finsupp.single (P i) 1`, and the number of preimages is a `Nat.card`.
--
--   Differences from the source:
--   - encoding: F/F_Q an algebraic function field of one variable with full constant field F_Q → k a finite field with Q = Nat.card k; F with [IsCurveOver k F], [Algebra.EssFiniteType k F] and ConstantsAreBase k F (platform AlgebraicCurve library); reason: every such function field satisfies these conditions, and a field satisfying them is finitely generated of transcendence degree 1 over k (Ω_{F/k} free of rank 1, k perfect) with L(0) = k; same objects
--   - encoding: distinct rational places P_1, …, P_N, D = P_1 + ⋯ + P_N → P : Fin N → Place k F injective with (P i).deg = 1 for all i; reason: a rational place is a place of degree one (§3, p.10); same data
--   - encoding: for each class γ ∈ C^m_F fix a representative G_γ as in Claim 4.2 → any G : Pic k F → Divisor k F with [G γ] = γ and ∀ i, G γ (P i) = 0 for every γ ∈ C^m_F; reason: the statement holds for each choice of representatives, which is what fixing an arbitrary one means
--   - encoding: F_γ = {f ∈ L(G_γ) : (f(P_1), …, f(P_N)) ∈ W_S(C_γ)} → f ∈ LSpace (G γ) ∧ ∀ i, (evalAt (P i) f ≠ 0 ↔ i ∈ S); reason: the evaluation vector of f ∈ L(G_γ) lies in C_γ, and W_S(C_γ) is the set of codewords with nonzero symbols exactly at S
--   - encoding: Φ is (Q − 1)-to-one (with the proof's well-definedness step) → (∀ x ∈ U, Φ x ∈ H) ∧ ∀ E ∈ H, Nat.card {x // x ∈ U ∧ Φ x = E} = Nat.card k − 1; reason: a map U → H that is (Q − 1)-to-one; both parts of the claim are stated
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Claim 4.4, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_BeatingGV42_degClasses
import Definitions.Def_BeatingGV42_divOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

/-- **Claim 4.4** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.2, p.15 (PDF p.17)): with `S ⊆ [N]`, `|S| = w`, the sets
`F_γ = {f ∈ L(G_γ) : (f(P_1), …, f(P_N)) ∈ W_S(C_γ)}` (`W_S(C_γ)` the codewords whose nonzero symbols
occur exactly at the indices in `S`), `U = ⋃_{γ ∈ C^m_F} F_γ × {γ}` and
"H = {H ∈ Div(F) : H ≥ 0, deg H = m − N + w and ν_{P_i}(H) = 0 for all i ∈ S}":
"The map Φ: U → H given by (f, γ) ↦ (f) + G_γ − Σ_{i∈[N]\S} P_i is (Q − 1)-to-one."
Both parts are stated: `Φ` maps `U` into `H` (the proof's "We first show that the map Φ is
well-defined"), and every `H ∈ H` has exactly `Q − 1` preimages in `U`.

**Formalization Note** The function field `F/F_Q` (one variable, full constant field `F_Q`) is encoded by the
platform's `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`, with `k`
any finite field and `Q = Nat.card k`; `g = genusFF k F`. The distinct rational places
`P_1, …, P_N` are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`
(`D = P_1 + ⋯ + P_N`). The section's standing choice "Fix an integer 2g − 2 < m < N" (p.13) is
kept as the hypotheses `hm`, `hmN`. The representatives `G_γ` (Claim 4.2) are any
`G : Pic k F → Divisor k F` with `[G γ] = γ` and `supp(G γ) ∩ supp(D) = ∅` for every `γ ∈ C^m_F`
(values off `C^m_F` are unused). `w = S.card` with `w ∈ [N]`, i.e. `1 ≤ |S|` (`|S| ≤ N` is automatic).
`U` is a set of pairs `(f, γ)`; the condition `(f(P_i))_i ∈ W_S(C_γ)` for `f ∈ L(G_γ)` is
"`f(P_i) ≠ 0 ↔ i ∈ S`" (the evaluation vector of `f ∈ L(G_γ)` lies in `C_γ`). `f(P)` is the
platform's `Place.evalAt`, `(f)` is `divOf f`, and `P_i` as a divisor is `Finsupp.single (P i) 1`.
`Q − 1` is `Nat.card k − 1` (`Nat.card k ≥ 2`). -/
theorem claim_4_4 (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F] (hC : ConstantsAreBase k F)
    {N : ℕ} (P : Fin N → Place k F) (hP : Function.Injective P) (hdeg : ∀ i, (P i).deg = 1)
    (m : ℕ) (hm : 2 * (genusFF k F : ℤ) - 2 < m) (hmN : m < N)
    (G : Pic k F → Divisor k F)
    (hG : ∀ γ ∈ degClasses k F m, (QuotientAddGroup.mk (G γ) : Pic k F) = γ ∧ ∀ i, G γ (P i) = 0)
    (S : Finset (Fin N)) (hS : 1 ≤ S.card) :
    let U : Set (F × Pic k F) := {x | x.2 ∈ degClasses k F m ∧ x.1 ∈ LSpace (G x.2) ∧
      ∀ i, ((P i).evalAt x.1 ≠ 0 ↔ i ∈ S)}
    let H : Set (Divisor k F) := {E | 0 ≤ E ∧ Divisor.degree E = (m : ℤ) - N + S.card ∧
      ∀ i ∈ S, E (P i) = 0}
    let Φ : F × Pic k F → Divisor k F := fun x =>
      divOf x.1 + G x.2 - ∑ i ∈ Sᶜ, Finsupp.single (P i) 1
    (∀ x ∈ U, Φ x ∈ H) ∧ ∀ E ∈ H, Nat.card {x : F × Pic k F // x ∈ U ∧ Φ x = E} = Nat.card k - 1 := by sorry

end BeatingGV42
