-- Prove2me | Theorems.Thm_ClassNumberFormula_ideal_count_asymptotic
-- name    : ClassNumberFormula.ideal_count_asymptotic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:53:29.355252+00:00
-- url     : https://prove2.me/theorems/f71856ae-3208-47c5-9280-c72ccf3f3362
-- title:
--   Ideal counting: average of the coefficients of $\zeta_K$
-- statement:
--   Let $K$ be a number field with $r_1$ real places, $r_2$ complex places, regulator $\mathrm{Reg}_K$, class number $h_K$, $w_K$ roots of unity and discriminant $D_K$. Then the number of nonzero ideals of $\mathcal O_K$ of norm at most $N$ satisfies
--   $$\lim_{N\to\infty}\frac{\#\{\mathfrak a\subseteq\mathcal O_K : 1\le N(\mathfrak a)\le N\}}{N} = \frac{2^{r_1}(2\pi)^{r_2}\,\mathrm{Reg}_K\,h_K}{w_K\sqrt{|D_K|}} .$$
--
--   In the source this is the lattice-point step of the general proof: the count is reduced, through the real and complex embeddings and Dirichlet's unit theorem, to counting lattice points in a region, which is approximated by the volume of the region.
--
--   **Formalization Note** The condition $1 \le N(\mathfrak a)$ excludes the zero ideal, whose norm is $0$ in Mathlib.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Proof", fourth paragraph (general case: reduction to a lattice point count)

import Mathlib
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem ideal_count_asymptotic (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ =>
        (Nat.card {I : Ideal (𝓞 K) // 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ N} : ℝ) / N)
      atTop (𝓝 ((2 : ℝ) ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K *
          classNumber K / (torsionOrder K * Real.sqrt |(discr K : ℝ)|))) := by sorry

end ClassNumberFormula
