-- Prove2me | Theorems.Thm_FewInnerTSP_Supplement_theorem_6_1
-- name    : FewInnerTSP.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:13:43.987965+00:00
-- url     : https://prove2.me/theorems/35312cd3-9cae-420c-bfd6-786f68fd820a
-- title:
--   Theorem 6.1 — an additively $\varepsilon$-optimal tour and $\bar c\in(\mathrm{OPT}-\varepsilon,\mathrm{OPT}]$ in $2^{O(\sqrt k)}\mathrm{poly}(n,L,\log^+(1/\varepsilon))$ bit operations
-- statement:
--   Let $P=(P_0,\dots,P_{n-1})$, $n\ge3$, be points of the Euclidean plane in general position (no three collinear) with **rational** coordinates, let $k$ be the number of points of $P$ that are not vertices of its convex hull, and let $\varepsilon>0$ be rational. Write $L$ for the largest binary encoding length of a coordinate or of $\varepsilon$, $\mathrm{len}(T)$ for the Euclidean length of a tour $T$, and $\mathrm{OPT}(P)=\min_T \mathrm{len}(T)$.
--
--   There is one deterministic multi-tape binary Turing machine $M$ and constants $C,c>0$ and $d\in\mathbb N$, fixed before the input, such that on the binary code of $(n,\varepsilon,P)$ the machine halts within
--   $$C\cdot 2^{c\sqrt k}\cdot\bigl(n+L+\log^+(1/\varepsilon)+2\bigr)^d$$
--   steps and outputs the code of a tour $T$ (a permutation of the indices) together with a rational number $\bar c$ such that
--   $$\mathrm{OPT}(P)\le\mathrm{len}(T)<\mathrm{OPT}(P)+\varepsilon\qquad\text{and}\qquad \bar c\in\bigl(\mathrm{OPT}(P)-\varepsilon,\ \mathrm{OPT}(P)\bigr].$$
--
--   This is the bit-complexity counterpart of Theorem 1.1: exact comparison of sums of square roots is not known to be possible in polynomial time, so the exact real-arithmetic algorithm is turned into an additive approximation whose cost keeps the $2^{O(\sqrt k)}$ dependence on the number of interior points and is otherwise polynomial in the input size and in $\log(1/\varepsilon)$. No bound on the geometric spread of the points is assumed beyond the encoding length.
--
--   **Formalization Note** One step of the machine is one bit operation. The first property is stated as $\mathrm{len}(T)<\mathrm{len}(\tau)+\varepsilon$ for every tour $\tau$; $\mathrm{OPT}(P)\le\mathrm{len}(T)$ is automatic since $T$ is a tour. The second is stated as $\bar c\le\mathrm{len}(\tau)$ for every tour $\tau$ and $\mathrm{len}(\tau)<\bar c+\varepsilon$ for some tour $\tau$. The output is required to be exactly the code of the pair $(T,\bar c)$, both produced by the same run.
--
--   Differences from the source:
--   - encoding: "bit operations" (no machine named) → steps of the published deterministic multi-tape binary Turing machine `MetaSearch.Heyting.Machine`; reason: a multi-tape Turing machine and a bit RAM simulate each other with polynomial overhead, and a polynomial of $2^{O(\sqrt k)}\mathrm{poly}(n,L,\log^+(1/\varepsilon))$ is again of that form, so the bound class is unchanged.
--   - encoding: $2^{O(\sqrt k)}\,\mathrm{poly}(n,L,\log^+(1/\varepsilon))$ → $C\cdot2^{c\sqrt k}(n+L+\log^+(1/\varepsilon)+2)^d$ with $C,c,d$ and the machine fixed before the input; reason: this is the standard meaning of the $O$-notation and of "poly"; every polynomial in $n,L,\log^+(1/\varepsilon)$ is at most $C(n+L+\log^+(1/\varepsilon)+2)^d$.
--   - encoding: "binary encoding length at most $L$ per coordinate", with the encoding of $\varepsilon$ included in $L$ → $L$ is the largest length, under a fixed prefix-free sign/numerator/denominator code, of a coordinate or of $\varepsilon$; reason: the page fixes no code, and any standard code is within a constant factor of this one.
--   - encoding: $n\ge3$ and general position from §1, p.1 → hypotheses `3 ≤ n` and the published `GeneralPos`; reason: the paper's standing assumptions for every result.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Theorem 6.1, p.13 (PDF p.15), eq. (17); proof in Appendix D.2, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_FewInnerTSP_Instance
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_FewInnerTSP_Supplement_BitModel

namespace FewInnerTSP.Supplement

/-- **Theorem 6.1 (Additive approximation in the bit model).** Li, Ma, Gong, *Exact Euclidean TSP
with Few Interior Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256
6541f631…), Theorem 6.1, p.13 (PDF p.15); proof in Appendix D.2, p.21 (PDF p.23): "For rational
general-position inputs and rational ε > 0, a Hamiltonian cycle T satisfying
OPT(P) ≤ len(T) < OPT(P) + ε can be computed in 2^{O(√k)} poly(n, L, log⁺(1/ε)) bit operations. The
same construction outputs a rational value c̄ ∈ (OPT(P) − ε, OPT(P)]."

There is one deterministic multi-tape binary Turing machine `M` and constants `C, c > 0`, `d`, fixed
before the input, such that for every `n ≥ 3`, every rational input `p : Fin n → ℚ × ℚ` whose points
`P = ptsOf p` are in general position, and every rational `ε > 0`, the machine run on
`inputCode n p ε` halts within `C · 2^{c √k} · (n + L + log⁺(1/ε) + 2)^d` steps (`k` the number of
interior points, `L = encLen p ε`), and its output is the code of a pair `(π, c̄)` with
1. `len(π) < len(τ) + ε` for every tour `τ`, i.e. `len(π) < OPT(P) + ε` (and `OPT(P) ≤ len(π)` holds
   because `π` is a tour);
2. `c̄ ≤ len(τ)` for every tour `τ`, and `len(τ) < c̄ + ε` for some tour `τ`, i.e.
   `c̄ ∈ (OPT(P) − ε, OPT(P)]`.

**Formalization Note**
* Bit operations are steps of the published deterministic multi-tape binary Turing machine
  `MetaSearch.Heyting.Machine`; `evalWithin M x t = some y` means `M` halts on `x` within `t` steps with
  `y` on its output tape. A multi-tape machine and a bit RAM simulate each other with polynomial
  overhead, and `(2^{c√k} poly)^{O(1)}` is again of that form, so the bound class is the page's.
* `L = encLen p ε` is the largest code length of a coordinate or of `ε` (§6, p.13: "Accuracy … data
  are also rational with their encoding included in L"). No bound on the spread is assumed.
* `poly(n, L, log⁺(1/ε))` is `(n + L + log⁺(1/ε) + 2)^d`; with `C` this dominates every polynomial.
* Both outputs come from one run on one input. The output is exact string equality with the
  injective code `outputCode`, not a decoder.
* `OPT(P)` is the minimum of `tourLen P τ` over the finitely many permutations `τ`; it is not
  introduced as a separate name. -/
theorem theorem_6_1 :
    ∃ M : MetaSearch.Heyting.Machine, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ d : ℕ,
      ∀ (n : ℕ), 3 ≤ n → ∀ (p : Fin n → ℚ × ℚ), GeneralPos (ptsOf p) →
      ∀ ε : ℚ, 0 < ε →
      ∃ t : ℕ,
        (t : ℝ) ≤ C * (2 : ℝ) ^ (c * Real.sqrt (interiorCount (ptsOf p) : ℝ)) *
          ((n : ℝ) + (encLen p ε : ℝ) + logPlusInv ε + 2) ^ d ∧
        ∃ (π : Equiv.Perm (Fin n)) (cbar : ℚ),
          M.evalWithin (inputCode n p ε) t = some (outputCode π cbar) ∧
          (∀ τ : Equiv.Perm (Fin n), tourLen (ptsOf p) π < tourLen (ptsOf p) τ + (ε : ℝ)) ∧
          (∀ τ : Equiv.Perm (Fin n), (cbar : ℝ) ≤ tourLen (ptsOf p) τ) ∧
          (∃ τ : Equiv.Perm (Fin n), tourLen (ptsOf p) τ < (cbar : ℝ) + (ε : ℝ)) := by sorry

end FewInnerTSP.Supplement
