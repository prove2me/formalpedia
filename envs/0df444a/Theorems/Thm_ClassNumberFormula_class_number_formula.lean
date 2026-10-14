-- Prove2me | Theorems.Thm_ClassNumberFormula_class_number_formula
-- name    : ClassNumberFormula.class_number_formula
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T13:01:23.435814+00:00
-- url     : https://prove2.me/theorems/69bfbae5-641a-44c4-8121-d9302e0106bc
-- title:
--   Class number formula: continuation of $\zeta_K$ with a simple pole at $s=1$ and its residue
-- statement:
--   Let $K$ be a number field of degree $n = r_1 + 2r_2$, where $r_1$ is the number of real embeddings and $2r_2$ the number of complex embeddings of $K$. Let $h_K$ be the class number, $\mathrm{Reg}_K$ the regulator, $w_K$ the number of roots of unity in $K$ and $D_K$ the discriminant of $K/\mathbb Q$. The Dedekind zeta function is the Dirichlet series
--   $$\zeta_K(s) = \sum_{n\ge1} \frac{a_n}{n^s}, \qquad a_n = \#\{\mathfrak a \subseteq \mathcal O_K \text{ ideal} : N(\mathfrak a) = n\}.$$
--
--   Then:
--
--   1. the series $\zeta_K(s)$ converges absolutely for $\operatorname{Re}(s) > 1$;
--   2. $\zeta_K$ extends to a meromorphic function on all of $\mathbb C$ whose only pole is a simple pole at $s=1$, with residue
--   $$\lim_{s\to1}(s-1)\zeta_K(s) = \frac{2^{r_1}(2\pi)^{r_2}\,\mathrm{Reg}_K\,h_K}{w_K\sqrt{|D_K|}}.$$
--
--   This is the general analytic class number formula, linking the analytic behaviour of $\zeta_K$ at $s = 1$ to the basic arithmetic invariants of $K$.
--
--   **Formalization Note** Part 2 is stated as: there is an entire function $G$ with $G(1)$ equal to the right-hand side and $\zeta_K(s) = G(s)/(s-1)$ for $\operatorname{Re}(s) > 1$. Then $G(s)/(s-1)$ is the meromorphic continuation; it is holomorphic away from $s=1$, and since $G(1) > 0$ it has a simple pole at $s = 1$ with residue $G(1)$. Mathlib's `dedekindZeta` is the series itself (a `tsum`), so it only carries meaning for $\operatorname{Re}(s) > 1$, which is why the continuation is an existential. Mathlib's `nrComplexPlaces K` is $r_2$ and `torsionOrder K` is $w_K$.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "General statement of the class number formula", Theorem (Class Number Formula)

import Mathlib
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem class_number_formula (K : Type*) [Field K] [NumberField K] :
    (∀ s : ℂ, 1 < s.re → Summable (fun n : ℕ => ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n‖)) ∧
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      G 1 = (((2 : ℝ) ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K *
          classNumber K / (torsionOrder K * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) ∧
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = G s / (s - 1) := by sorry

end ClassNumberFormula
