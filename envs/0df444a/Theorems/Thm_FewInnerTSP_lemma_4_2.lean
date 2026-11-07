-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_4_2
-- name    : FewInnerTSP.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:33:38.11892+00:00
-- url     : https://prove2.me/theorems/74e0305e-ad02-4b33-8d2b-c0e3ca08f491
-- title:
--   Lemma 4.2 (Core contribution)
-- statement:
--   In normalized coordinates (separator $\sigma_t$ of side $t$ centered at $0$), let $A$ be any finite set of $a\ge1$ core points, placed arbitrarily. The core charge
--   $$E_A(t)=\sum_{s,\ g\ \text{active}}\log_2(1+a_g),\qquad a_g=|A\cap D_g|,$$
--   summed over all dyadic scales $s=2^{-j}$, $j\ge0$, and all frames $D_g$ active at $t$, satisfies
--   $$\mathbb E_t\,E_A(t)=O(\sqrt a)$$
--   for $t$ uniform on $[1,3]$: there is an absolute constant $C>0$ with $\mathbb E_t E_A(t)\le C\sqrt a$ for every such $A$.
--
--   This is the planar half of the mixed charge: the core costs $O(\sqrt a)$ in the logarithm of the number of crossing-edge choices.
--
--   **Formalization Note** The expectation is $\tfrac12\int_1^3E_A(t)\,dt$ of a $[0,\infty]$-valued charge.
--
--   Differences from the source:
--   - encoding: E_t E_A(t) = O(√a) → (1/2)∫⁻ over [1,3] of the ℝ≥0∞-valued charge ≤ C √a, with C fixed before A; reason: O-notation with the constant before the input
--   - encoding: a ≥ 1 (§4 standing hypothesis) → the hypothesis 1 ≤ |A|; reason: the bound is stated for nonempty cores, as in §4
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 4.2, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_FewInnerTSP_Charges

namespace FewInnerTSP

open scoped ENNReal

/-- **Lemma 4.2 (Core contribution).** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior Points: A
Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 4.2, p.7 (PDF p.9):
"For arbitrary core locations, EtEA(t) = O(√a)."

There is a constant `C > 0` such that for every finite set `A` of `a ≥ 1` points in the normalized plane,
the expectation over `t` uniform on `[1, 3]` of the core charge
`E_A(t) = Σ_{s, g active} log₂(1 + a_g)` (all dyadic scales `s = 2^{-j}`, `j ≥ 0`, all half-open frames
`D_g`, active when `D_g` meets `∂σ_t`) is at most `C √a`.

**Formalization Note** The charge is in `ℝ≥0∞` and the expectation is `(1/2) ∫⁻ t in [1,3]`. No
assumption is made on the positions of `A`; `C` comes before `A`. -/
theorem lemma_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset Pt, 1 ≤ A.card →
      expectedCharge A ≤ ENNReal.ofReal (C * Real.sqrt (A.card : ℝ)) := by sorry

end FewInnerTSP
