-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_theorem_2_3
-- name    : CorrBoundsPoly.ExactDegree.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:00.980633+00:00
-- url     : https://prove2.me/theorems/070079b1-c88f-450a-a0bd-5c0c67ee6c11
-- title:
--   Theorem 2.3 — general leading-rank criterion: $\rho_d(f^{\oplus t})\le(1-2r/L)^t$ and $\rho_d(\bigoplus_i f_i)\le\prod_i(1-2\alpha_i)$
-- statement:
--   Let $f:\mathbb F_2^m\to\mathbb F_2$ and $L=\dim_{\mathbb F_2}B=2^m$. Suppose a coordinate-compatible finite rationally indexed filtration of $B$ gives the multiplication operator $\mu_f$ leading shift $D$ with $D>d\ge0$, and leading operator $T=\operatorname{gr}_D(\mu_f)$ of rank $r$. Then for every $t\ge1$,
--   $$\rho_d\big(f^{\oplus t}\big)\le\Big(1-\frac{2r}{L}\Big)^t. \tag{2.2}$$
--   More generally, let $f_1,\dots,f_k$ be cores on $m_1,\dots,m_k$ variables, each with such a certificate: a coordinate-compatible filtration of its own function algebra giving $\mu_{f_i}$ leading shift $D_i>d$ and leading operator of rank $r_i$, normalized rank $\alpha_i=r_i/2^{m_i}$. Then, on disjoint blocks,
--   $$\rho_d\Big(\bigoplus_i f_i\Big)\le\prod_i(1-2\alpha_i).$$
--   The maximum in $\rho_d$ ranges over every polynomial of degree at most $d$ in all the variables: competing polynomials have unrestricted cross-block terms.
--
--   This is the paper's general sufficient condition for XOR amplification against all low-degree tests; the upper bounds for elementary cores (Corollary 3.7) and for the exact-degree cores (Theorem 4.1) are instances of it.
--
--   **Formalization Note** The leading operator's rank is `Module.finrank` of the range of `symbol Φ (mulOp f) D hD.1` on the graded space (finite-dimensional: only threshold weights carry nonzero pieces). $f^{\oplus t}$ is `xorPow t f` on `Fin t × Fin m`; $\bigoplus_i f_i$ is `xorBlocks f` on `Σ i, Fin (m i)`.
--
--   Differences from the source:
--   - encoding: $B=\mathbb F_2[x]/(x_i^2-x_i)$ → `BFun m`, functions with pointwise operations; reason: identification by evaluation (p. 26)
--   - encoding: disjoint blocks of $tm$ (resp. $\sum_i m_i$) variables → variable sets `Fin t × Fin m` and `Σ i, Fin (m i)`; reason: relabelling of the variables
--   - encoding: $\rho_d$ as a maximum over degree-$\le d$ Boolean functions → `Finset.sup` of `|corr|` over all `P` with `HasDegLE P d`; reason: finite nonempty set, the sup is the maximum
--   - reading: "disjoint cores with such certificates of normalized ranks $\alpha_i$" → each core $f_i$ has its own coordinate-compatible filtration with its own leading shift $D_i>d$ (the $D_i$ may differ) and $\alpha_i=r_i/2^{m_i}$; reason: the proof's Step 6 (p. 23) treats different leading shifts $D_i>d$ by rescaling weights to $D_*=\min_i D_i$
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 22 (PDF 24), Theorem 2.3, Eq. (2.2)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Rho
import Definitions.Def_CorrBoundsPoly_ExactDegree_Filtration

namespace CorrBoundsPoly.ExactDegree

/-- **Theorem 2.3** (General leading-rank sufficient condition; Xin Li, *More on Correlation Bounds
for Polynomials*, p. 22, PDF 24). (1) Let `f : F₂^m → F₂`, `L = 2^m`. If a coordinate-compatible
filtration of `B` gives `µ_f` leading shift `D > d ≥ 0` and leading operator `T` of rank `r`, then
`ρ_d(f^{⊕t}) ≤ (1 − 2r/L)^t` for every `t ≥ 1` (Eq. (2.2)). (2) More generally, for disjoint cores
`f_i` on `m_i` variables with such certificates (leading shifts `D_i > d`, leading ranks `r_i`,
`α_i = r_i / 2^{m_i}`), `ρ_d(⨁_i f_i) ≤ ∏_i (1 − 2α_i)`. `ρ_d` ranges over all tests of degree
at most `d` on all the variables, cross-block monomials included. -/
theorem theorem_2_3 :
    (∀ (m d : ℕ) (f : BFun m) (Φ : RatFiltration (ZMod 2) (BFun m)), CoordCompatible Φ →
      ∀ (D : ℚ) (hD : Φ.IsLeadingShift (mulOp f) D), (d : ℚ) < D →
      ∀ t : ℕ, 1 ≤ t →
        rho d (xorPow t f) ≤
          (1 - 2 * (Module.finrank (ZMod 2) (LinearMap.range (Φ.symbol (mulOp f) D hD.1)) : ℝ) /
            2 ^ m) ^ t) ∧
    (∀ (k d : ℕ) (m : Fin k → ℕ) (f : ∀ i, BFun (m i))
      (Φ : ∀ i, RatFiltration (ZMod 2) (BFun (m i))), (∀ i, CoordCompatible (Φ i)) →
      ∀ (D : Fin k → ℚ) (hD : ∀ i, (Φ i).IsLeadingShift (mulOp (f i)) (D i)),
      (∀ i, (d : ℚ) < D i) →
        rho d (xorBlocks f) ≤
          ∏ i : Fin k, (1 - 2 * ((Module.finrank (ZMod 2)
            (LinearMap.range ((Φ i).symbol (mulOp (f i)) (D i) (hD i).1)) : ℝ) / 2 ^ m i))) := by sorry

end CorrBoundsPoly.ExactDegree
