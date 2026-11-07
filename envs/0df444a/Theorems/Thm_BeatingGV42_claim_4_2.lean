-- Prove2me | Theorems.Thm_BeatingGV42_claim_4_2
-- name    : BeatingGV42.claim_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:48.265406+00:00
-- url     : https://prove2.me/theorems/b99e79bb-ff13-401e-80d1-d3969101c37b
-- title:
--   Claim 4.2 — every class of degree $m$ has a representative with support disjoint from $D$
-- statement:
--   Let $F/\mathbb F_Q$ be a function field of genus $g$ with distinct rational places $P_1,\dots,P_N$, let $D=P_1+\dots+P_N$, and fix an integer $m$ with $2g-2<m<N$. Then every divisor class $\gamma\in\mathcal C^m_F$ has a representative $G_\gamma\in\operatorname{Div}(F)$ with
--   $$
--   \operatorname{supp}(G_\gamma)\cap\operatorname{supp}(D)=\emptyset .
--   $$
--   These representatives define the mother codes $C_\gamma=C_L(D,G_\gamma)$, one for each class.
--
--   **Formalization Note** The function field $F/\mathbb F_Q$ is encoded by the platform's `AlgebraicCurve` library: a finite field `k` with $Q$ = `Nat.card k`, and $F$ with `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`; $g$ = `genusFF k F`. The places are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`. The section's standing choice $2g-2<m<N$ (p.13) is kept as hypotheses; $\operatorname{supp}(G)\cap\operatorname{supp}(D)=\emptyset$ is `∀ i, G (P i) = 0`.
--
--   Differences from the source:
--   - encoding: F/F_Q an algebraic function field of one variable with full constant field F_Q → k a finite field with Q = Nat.card k; F with [IsCurveOver k F], [Algebra.EssFiniteType k F] and ConstantsAreBase k F (platform AlgebraicCurve library); reason: every such function field satisfies these conditions, and a field satisfying them is finitely generated of transcendence degree 1 over k (Ω_{F/k} free of rank 1, k perfect) with L(0) = k; same objects
--   - encoding: distinct rational places P_1, …, P_N, D = P_1 + ⋯ + P_N → P : Fin N → Place k F injective with (P i).deg = 1 for all i; reason: a rational place is a place of degree one (§3, p.10); same data
--   - encoding: supp(G) ∩ supp(D) = ∅ → ∀ i, G (P i) = 0; reason: D is supported exactly on the P_i; same condition
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Claim 4.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_BeatingGV42_degClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

/-- **Claim 4.2** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.2, p.13 (PDF p.15)): "Every divisor class γ ∈ C^m_F has a representative
G_γ ∈ Div(F) satisfying supp(G_γ) ∩ supp(D) = ∅."

**Formalization Note** The function field `F/F_Q` (one variable, full constant field `F_Q`) is encoded by the
platform's `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`, with `k`
any finite field and `Q = Nat.card k`; `g = genusFF k F`. The distinct rational places
`P_1, …, P_N` are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`
(`D = P_1 + ⋯ + P_N`). The section's standing choice "Fix an integer 2g − 2 < m < N" (p.13) is
kept as the hypotheses `hm`, `hmN`. `supp(G) ∩ supp(D) = ∅` is `∀ i, G (P i) = 0`; "`G` represents `γ`" is
`QuotientAddGroup.mk G = γ` in `Pic k F`. -/
theorem claim_4_2 (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F] (hC : ConstantsAreBase k F)
    {N : ℕ} (P : Fin N → Place k F) (hP : Function.Injective P) (hdeg : ∀ i, (P i).deg = 1)
    (m : ℕ) (hm : 2 * (genusFF k F : ℤ) - 2 < m) (hmN : m < N) :
    ∀ γ ∈ degClasses k F m, ∃ G : Divisor k F,
      (QuotientAddGroup.mk G : Pic k F) = γ ∧ ∀ i, G (P i) = 0 := by sorry

end BeatingGV42
