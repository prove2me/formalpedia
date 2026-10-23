-- Prove2me | Theorems.Thm_CircletTSP_Facet_lemma_3_4
-- name    : CircletTSP.Facet.lemma_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:10.481578+00:00
-- url     : https://prove2.me/theorems/d365ebdd-a210-4a38-af4e-c24c28889a24
-- title:
--   Lemma 3.4, p. 10 — a minimal counterexample has none of the structures of Figure 4
-- statement:
--   Let $n$ be a positive multiple of $4$ and $d=n/2$. Let $H$ be a Hamiltonian cycle on $K_n$ with
--   $$\sum_{i=1}^{d} c_i t_i < n-2,$$
--   and suppose it is minimal with respect to $n$: for every $m$ with $0<m<n$ and $4\mid m$, every Hamiltonian cycle on $K_m$ satisfies Inequality (2) for $m$. Then for every vertex $u$, $H$ contains none of the three edge sets
--   $$\{u+d,u\},\{u,u+1\},\{u+1,u+1+d\};\qquad \{u+1,u\},\{u,u+d\},\{u+d,u+1+d\};\qquad \{u,u+1\},\{u+1,u+1+d\},\{u+1+d,u+d\}$$
--   (structures A, B1, B2 of Figure 4; labels mod $n$).
--
--   This is the technical lemma behind Theorem 3.1. Its hypotheses cannot hold once Theorem 3.1 is known; it is stated as printed.
--
--   **Formalization Note** "Minimal with respect to $n$" quantifies over smaller multiples of $4$ only, as in the paper's induction on $n$.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 10, Lemma 3.4

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Lemma 3.4 (p. 10): a Hamiltonian cycle violating Inequality (2) on a number of vertices `n`
that is minimal (every Hamiltonian cycle on `m` vertices, `0 < m < n`, `4 ∣ m`, satisfies
Inequality (2)) contains none of the structures A, B1, B2 of Figure 4, at any vertex `u`. -/
theorem lemma_3_4 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (hlt : circletForm n (MetricTSP.tourVec π) < (n : ℝ) - 2)
    (hmin : ∀ m : ℕ, 0 < m → m < n → 4 ∣ m → ∀ σ : Equiv.Perm (Fin m),
      (m : ℝ) - 2 ≤ circletForm m (MetricTSP.tourVec σ)) :
    ∀ u : Fin n, ¬ IsStructA π u ∧ ¬ IsStructB1 π u ∧ ¬ IsStructB2 π u := by sorry

end CircletTSP.Facet
