-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctions_m_minimizer_cut
-- name    : DiscreteConvex.MConvexFunctions.m_minimizer_cut
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:57:19.935374+00:00
-- url     : https://prove2.me/theorems/0d04c4a7-68cb-42c2-b504-a2e4cfe1b6f3
-- title:
--   Theorem 6.28 -- the M-minimizer cut
-- statement:
--   **Theorem 6.28** (p.149). Let $f$ be an M-convex function with $\arg\min f \ne \emptyset$. (1) For $x \in \operatorname{dom} f$, $v \in V$, and $u$ minimizing $s \mapsto f(x-\chi_s+\chi_v)$, some minimizer $x^*$ has $x^*(u) \le x(u)-1+\chi_v(u)$. (2) Symmetrically for $u \in V$ and $v$ minimizing $t \mapsto f(x-\chi_u+\chi_t)$, some minimizer $x^*$ has $x^*(v) \ge x(v)-\chi_u(v)+1$. (3) For $x \in \operatorname{dom} f \setminus \arg\min f$ and $u,v$ jointly minimizing $(s,t) \mapsto f(x-\chi_s+\chi_t)$, some minimizer $x^*$ has $x^*(u) \le x(u)-1$ and $x^*(v) \ge x(v)+1$. This is the basis of the domain-reduction algorithm for M-convex function minimization and a direct ingredient of the M-proximity theorem's proof.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.149, Theorem 6.28.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.149, Theorem 6.28

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec

namespace DiscreteConvex.MConvexFunctions

/-- Theorem 6.28, the M-minimizer cut (Murota, *Discrete Convex Analysis*, SIAM 2003, p.149).
Let `f` be an M-convex function with `arg min f ≠ ∅`. (1) For `x ∈ dom f`, `v ∈ V`, and `u`
minimizing `s ↦ f(x - χ_s + χ_v)`, some `x* ∈ arg min f` has `x*(u) ≤ x(u) - 1 + χ_v(u)`.
(2) Symmetrically for `u ∈ V` and `v` minimizing `t ↦ f(x - χ_u + χ_t)`, some
`x* ∈ arg min f` has `x*(v) ≥ x(v) - χ_u(v) + 1`. (3) For `x ∈ dom f \ arg min f` and `u, v`
jointly minimizing `(s,t) ↦ f(x - χ_s + χ_t)`, some `x* ∈ arg min f` has `x*(u) ≤ x(u) - 1` and
`x*(v) ≥ x(v) + 1`. -/
theorem m_minimizer_cut {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) (hne : (ArgMin f).Nonempty) :
    (∀ x ∈ DomZ f, ∀ v u : V,
        (∀ s : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec v w)) →
        ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 + CharVec v u) ∧
    (∀ x ∈ DomZ f, ∀ u v : V,
        (∀ t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec u w + CharVec t w)) →
        ∃ xs ∈ ArgMin f, xs v ≥ x v - CharVec u v + 1) ∧
    (∀ x ∈ DomZ f \ ArgMin f, ∀ u v : V,
        (∀ s t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec t w)) →
        ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 ∧ xs v ≥ x v + 1) := by sorry

end DiscreteConvex.MConvexFunctions
