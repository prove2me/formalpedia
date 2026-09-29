-- Prove2me | Theorems.Thm_ArithmeticE_algebraic_e_combination_zero_singularity
-- name    : ArithmeticE.algebraic_e_combination_zero_singularity
-- status  : Open
-- author  : @shivm
-- created : 2026-09-11T16:34:52.858631+00:00
-- url     : https://prove2.me/theorems/b9e008ee-fd9f-40f0-bb17-bdd6b0c8f934
-- title:
--   Arithmetic zero-singularity theorem for algebraic combinations of rational E-series
-- statement:
--   Let $f_1,\ldots,f_m$ have rational factorial-normalized coefficients with exponential size and common-denominator bounds. Let $P_i\in\overline{\mathbb Q}[X]$, and put $F=\sum_iP_if_i$. Suppose $F$ has a minimal complex polynomial differential equation of positive order $n$, with leading coefficient $p_n$. At a nonzero algebraic point $\xi$, assume
--   $$\sum_i P_i(\xi)f_i(\xi)=0.$$
--   Then $p_n(\xi)=0$.
--
--   The equation supplies holonomicity of $F$; the coefficient hypotheses supply its E-function arithmetic and convergence. The positive-order and minimality assumptions exclude the identically zero function. This is the zero-singularity consequence of the established André–Beukers theory, stated for the combinations needed in linear lifting. It remains a substantial open formalization task. It does not follow from ordinary analytic ODE existence alone.
--
--   ### Established supporting results and remaining bridge
--
--   The following auxiliary theorems now have accepted complete Lean proofs:
--
--   - [Division preserves minimal differential order](https://prove2.me/theorems/6e7d145b-73da-498c-872d-7808c339ba00): a least-order equation for $(1-X)g$ transfers to a least-order equation of the same order for $g$, with transformed leading polynomial $(1-X)p_n$.
--   - [Minimal-operator coefficient-field descent](https://prove2.me/theorems/1d573d1e-d78e-4657-80e0-c9a81558c2e0): a complex minimal equation for a formal series over a subfield $K$ descends to $K[X]$, at the same order. This is coefficientwise formal algebra; it does not assert that a discontinuous linear projection commutes with analytic evaluation.
--   - [Irreducible spanning-orbit factor lemma](https://prove2.me/theorems/d6dff768-7add-4b75-8bee-42c55dfdad41): a pointwise vanishing finite product of linear evaluations on spanning orbits, with closed zero loci over an irreducible space, forces one evaluation to vanish identically.
--
--   These are supporting results, not yet a checked reduction of the present theorem. The missing classical bridge must construct the relevant E-function solution spaces and conjugate orbits, prove the irreducibility/closedness/spanning/product hypotheses in that setting, and supply André's full holomorphic-basis theorem at finite nonzero points. Merely knowing that a solution vanishes does not force its differential equation to be singular. No proof dependency is being claimed until those mathematical interfaces are instantiated.
--
--   The links record completed work available to a future proof of this leaf. They introduce no new conjectural arithmetic assumption and do not close this known-but-unformalized classical theorem.
-- source:
--   Beukers, A refined version of the Siegel–Shidlovskii theorem, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf. Theorem 2.1, Corollary 2.2, and Theorem 2.5, pp. 3–5. The algebraic-coefficient extension uses differential Galois theory in Lemmas 2.3–2.4.

import Definitions.Def_beukersLiftingData
open ArithmeticE

theorem ArithmeticE.algebraic_e_combination_zero_singularity
    (m : ℕ) (f : Fin m → PowerSeries ℂ) (harith : ∀ i, RationalSeriesArithmetic (f i))
    (P : Fin m → Polynomial ℂ) (hP : ∀ i k, IsAlgebraic ℚ ((P i).coeff k))
    (ξ : ℂ) (hξ : IsAlgebraic ℚ ξ) (hξ0 : ξ ≠ 0)
    (hz : ∑ i, (P i).eval ξ * seriesValue (f i) ξ = 0)
    (p : ℕ → Polynomial ℂ) (n : ℕ) (hn : 0 < n)
    (hmin : MinimalEquation p n (∑ i, (P i : PowerSeries ℂ) * f i)) :
    (p n).eval ξ = 0 := by sorry
