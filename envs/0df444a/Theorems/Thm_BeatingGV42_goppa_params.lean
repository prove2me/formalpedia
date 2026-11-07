-- Prove2me | Theorems.Thm_BeatingGV42_goppa_params
-- name    : BeatingGV42.goppa_params
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:38.902354+00:00
-- url     : https://prove2.me/theorems/729fd334-86cf-44fc-b7b1-87aa91353701
-- title:
--   §3 / eq. (4.6) — dimension $\deg G+1-g$ and distance $\ge N-\deg G$ of $C_L(D,G)$
-- statement:
--   Let $F/\mathbb F_Q$ be a function field of genus $g$, $P_1,\dots,P_N$ distinct rational places, $D=P_1+\dots+P_N$, and $G$ a divisor with $\operatorname{supp}(G)\cap\operatorname{supp}(D)=\emptyset$ and $2g-2<\deg G<N$. Then the Goppa code $C_L(D,G)$ satisfies
--
--   1. $\dim C_L(D,G)=\ell(G)$,
--   2. $\dim C_L(D,G)=\deg G+1-g$,
--   3. every nonzero codeword has weight at least $N-\deg G$, i.e. $d(C_L(D,G))\ge N-\deg G$.
--
--   With $G=G_\gamma$ of degree $m$ this is eq. (4.6), $\dim(C_\gamma)=\ell(G_\gamma)=m+1-g$ and $d(C_\gamma)\ge N-m$: the dimension gives $|C_\gamma|=Q^{m+1-g}$ in (4.21), and the distance makes $A_w(C_\gamma)=0$ for $1\le w<N-m$ in the proof of Claim 4.10.
--
--   **Formalization Note** The function field $F/\mathbb F_Q$ is encoded by the platform's `AlgebraicCurve` library: a finite field `k` with $Q$ = `Nat.card k`, and $F$ with `IsCurveOver k F`, `Algebra.EssFiniteType k F` and `ConstantsAreBase k F`; $g$ = `genusFF k F`. The places are an injective `P : Fin N → Place k F` with every `(P i).deg = 1`. $\ell(G)$ = `ell G`; the distance of a linear code is stated as the weight bound for nonzero codewords (`hammingNorm`).
--
--   Differences from the source:
--   - encoding: F/F_Q an algebraic function field of one variable with full constant field F_Q → k a finite field with Q = Nat.card k; F with [IsCurveOver k F], [Algebra.EssFiniteType k F] and ConstantsAreBase k F (platform AlgebraicCurve library); reason: every such function field satisfies these conditions, and a field satisfying them is finitely generated of transcendence degree 1 over k (Ω_{F/k} free of rank 1, k perfect) with L(0) = k; same objects
--   - encoding: distinct rational places P_1, …, P_N, D = P_1 + ⋯ + P_N → P : Fin N → Place k F injective with (P i).deg = 1 for all i; reason: a rational place is a place of degree one (§3, p.10); same data
--   - encoding: supp(G) ∩ supp(D) = ∅ → ∀ i, G (P i) = 0; reason: D is supported exactly on the P_i; same condition
--   - encoding: minimum distance at least N − deg G → every nonzero codeword c has (N : ℤ) − deg G ≤ hammingNorm c; reason: for a linear code the minimum distance is the minimum weight of a nonzero codeword
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §3, p.11 (PDF p.13), and eq. (4.6), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_BeatingGV42_goppaCode

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

namespace BeatingGV42

open Classical in
/-- **Parameters of Goppa codes** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.11 (PDF p.13): "When 2g − 2 < deg G < N, this code has
dimension deg G + 1 − g and minimum distance at least N − deg G"; as used in eq. (4.6), p.14
(PDF p.16): "each C_γ is a linear code with dim(C_γ) = ℓ(G_γ) = m + 1 − g and d(C_γ) ≥ N − m").

For distinct rational places `P_1, …, P_N` and a divisor `G` with `supp(G) ∩ supp(D) = ∅` and
`2g − 2 < deg G < N`: `dim C_L(D, G) = ℓ(G) = deg G + 1 − g`, and every nonzero codeword has weight
at least `N − deg G`.

**Formalization Note** The function field `F/F_Q` is encoded by the platform's `IsCurveOver k F`,
`Algebra.EssFiniteType k F` and `ConstantsAreBase k F`, with `k` any finite field; `g = genusFF k F`,
`ℓ(G) = ell G = dim_k L(G)`. The places are an injective `P : Fin N → Place k F` with every
`(P i).deg = 1`; `supp(G) ∩ supp(D) = ∅` is `∀ i, G (P i) = 0`. "Minimum distance at least
`N − deg G`" of a linear code is stated as the weight bound for nonzero codewords (`hammingNorm`). -/
theorem goppa_params (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F] (hC : ConstantsAreBase k F)
    {N : ℕ} (P : Fin N → Place k F) (hP : Function.Injective P) (hdeg : ∀ i, (P i).deg = 1)
    (G : Divisor k F) (hG : ∀ i, G (P i) = 0)
    (hG1 : 2 * (genusFF k F : ℤ) - 2 < Divisor.degree G) (hG2 : Divisor.degree G < N) :
    Module.finrank k (goppaCode P G) = ell G ∧
    (Module.finrank k (goppaCode P G) : ℤ) = Divisor.degree G + 1 - genusFF k F ∧
    ∀ c ∈ goppaCode P G, c ≠ 0 → (N : ℤ) - Divisor.degree G ≤ (hammingNorm c : ℤ) := by sorry

end BeatingGV42
