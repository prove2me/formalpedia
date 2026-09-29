-- Prove2me | Theorems.Thm_AlgebraicCurve_bddAbove_chowLogAt_range
-- name    : AlgebraicCurve.bddAbove_chowLogAt_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/e145f2f5-93fc-56ea-bfd9-5e6ba9f89657
-- title:
--   Boundedness of normalised Chow form values along a pencil
-- statement:
--   Let $F$ be a field equipped with an algebra structure over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $r$ be a natural number, let $\sigma : \overline{\mathbb{Q}} \to \mathbb{C}$ be a ring homomorphism, let $s : \mathrm{Fin}\,r \to F$ be a family of elements of $F$, let $Z$ be a divisor, i.e. a finitely supported function from places of $F$ over $\overline{\mathbb{Q}}$ (valuation subrings of $F$ containing the image of $\overline{\mathbb{Q}}$, proper, and principal ideal rings) to $\mathbb{Z}$, and let $v$ be one such place. Here `chowForm s Z` is the polynomial $\prod_w \bigl(\sum_i \mathrm{C}(\,\mathrm{evalVec}\, s\, w\, i)\,X_i\bigr)^{(Z\,w)^{+}}$ in $\overline{\mathbb{Q}}[X_0,\dots,X_{r-1}]$, the product being over the support of $Z$ with exponents the natural-number truncations $(Z\,w)^{+}$ of the multiplicities, and $\mathrm{evalVec}\, s\, w\, i$ is the residue of $s_i\, s_{\mathrm{pivotIndex}(s,w)}^{-1}$ at $w$ (lifted back into $\overline{\mathbb{Q}}$, and $0$ when $r = 0$). The assertion is that the set of real numbers $$\frac{\lVert \sigma\bigl((\mathrm{chowForm}\, s\, Z)(a)\bigr)\rVert}{\bigl(\sup_i \lVert \sigma(a_i)\rVert\bigr)^{\sum_w (Z\,w)^{+}}},$$ as $a : \mathrm{Fin}\,r \to \overline{\mathbb{Q}}$ runs over the nonzero vectors satisfying the single linear relation $\sum_i (\mathrm{evalVec}\, s\, v\, i)\, a_i = 0$, is bounded above.
--
--   This is the boundedness statement that makes the normalised archimedean size of the Chow form of a zero-cycle, measured along the vectors annihilating the point attached to a place $v$, a genuine real supremum, so that its logarithm is defined. It is used in the height-theoretic estimates for the cycle $J_0$: by [`ModularCurve.JZero.chowSide_arch_embedding_off_support`](thm.html#ModularCurve.JZero.chowSide_arch_embedding_off_support), [`ModularCurve.JZero.prox_sum_chowSide`](thm.html#ModularCurve.JZero.prox_sum_chowSide) and [`ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le`](thm.html#ModularCurve.JZero.prox_sum_le_of_forall_log_secVal_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_bddAbove_chowLogAt_range.lean

import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.bddAbove_chowLogAt_range {F : Type} [Field F]
    [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → F)
    (Z : Divisor (AlgebraicClosure ℚ) F) (v : Place (AlgebraicClosure ℚ) F) :
    BddAbove (Set.range
      fun a : {a : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * a i = 0 ∧ a ≠ 0} =>
        ‖σ (MvPolynomial.eval a.1 (chowForm s Z))‖
          / (⨆ i, ‖σ (a.1 i)‖) ^ (Z.sum fun _ n => n.toNat)) := by sorry
