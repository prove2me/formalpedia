-- Prove2me | Theorems.Thm_CuspForm_exists_differentiable_eq_lSeries_qCoeff
-- name    : CuspForm.exists_differentiable_eq_lSeries_qCoeff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-11T18:03:44.424515+00:00
-- url     : https://prove2.me/theorems/c58af730-1cdb-4b7b-b96e-c5c2be7dd0da
-- title:
--   Hecke: the L-series of a weight-two cusp form on $\Gamma_0(N)$ extends to an entire function
-- statement:
--   Let $N \ge 1$ and let $f$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(N)$, with $q$-expansion
--
--   $$f(\tau) \;=\; \sum_{n \ge 1} a_n q^{n}, \qquad q = e^{2\pi i \tau},$$
--
--   and let
--
--   $$L(f,s) \;=\; \sum_{n \ge 1} \frac{a_n}{n^{s}}$$
--
--   be its L-series. For a cusp form of weight $2$ one has $a_n = O(n)$, so the series converges absolutely on the half-plane $\operatorname{Re} s > 2$. The assertion is Hecke's theorem: $L(f,s)$ is the restriction of an entire function. That is, there exists $\Lambda : \mathbb{C} \to \mathbb{C}$, complex differentiable at every point of $\mathbb{C}$, with
--
--   $$\Lambda(s) \;=\; L(f,s) \qquad \text{for every } s \text{ with } \operatorname{Re} s > 2 .$$
--
--   Nothing is asserted about a functional equation, nor about the values of $\Lambda$ on $\operatorname{Re} s \le 2$ beyond entireness; by the identity theorem such a $\Lambda$ is unique.
--
--   The statement is the analytic half of the passage from modular forms to L-functions: combined with a coefficient identity it yields the holomorphic continuation of the L-series of any Dirichlet series whose coefficients are those of a weight-two cusp form, in particular the Hasse-Weil L-series of an elliptic curve over $\mathbb{Q}$.
--
--   **Formalization Note** $a_n$ is `ModularFormClass.qCoeff f n`, the $n$-th coefficient of `UpperHalfPlane.qExpansion 1 f` (the width at the cusp $\infty$ of $\Gamma_0(N)$ is $1$), and $L(f,s)$ is Mathlib's `LSeries`, which takes the junk value $0$ where the Dirichlet series is not summable; the agreement is therefore only required on the half-plane $\operatorname{Re} s > 2$, where summability holds. Entireness is `Differentiable ℂ Λ`.
-- source:
--   E. Hecke, Uber die Bestimmung Dirichletscher Reihen durch ihre Funktionalgleichung, Math. Ann. 112 (1936), 664-699 (the correspondence between modular forms and Dirichlet series obtained by Mellin transform, giving the holomorphic continuation of L(f,s) for a cusp form f). The continuation of L(f,s) for weight-two cusp forms is invoked in A. Wiles, The Birch and Swinnerton-Dyer Conjecture, Clay Millennium Prize Problem description, p. 2.

import Definitions.Def_FLTPrelim_Modularity
import Mathlib

namespace CuspForm
theorem exists_differentiable_eq_lSeries_qCoeff {N : ℕ} (hN : 0 < N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, 2 < s.re → Λ s = LSeries (ModularFormClass.qCoeff f) s := by sorry
end CuspForm
