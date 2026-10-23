-- Prove2me | Theorems.Thm_CircletTSP_Facet_tight_tours
-- name    : CircletTSP.Facet.tight_tours
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:27.882963+00:00
-- url     : https://prove2.me/theorems/59b0707f-dc60-4d7c-bf97-31960674dcfa
-- title:
--   Proof of Theorem 5.1, pp. 20–21 — n(n − 3)/2 tight tours with linearly independent incidence vectors
-- statement:
--   Let $n$ be a positive multiple of $4$. There are $n(n-3)/2$ Hamiltonian cycles $H_1,\dots,H_{n(n-3)/2}$ on $K_n$ such that
--
--   1. each is tight for Inequality (2): $\sum_{i=1}^{d} c_i t_i(\chi_{H_r})=n-2$;
--   2. their incidence vectors $\chi_{H_1},\dots,\chi_{H_{n(n-3)/2}}$ are linearly independent.
--
--   The paper exhibits $n/2$ rotations of a tour with two edges of length $d$ and, for each $k\in\{3,\dots,d\}$, $n$ rotations of a tour with a single edge of cost $k-1$, for $n/2+(n/2-2)n=n(n-3)/2$ tours in total. With the dimension of $STSP(n)$ this gives the facet property.
--
--   **Formalization Note** Stated existentially ("we find … tours"); the family is not fixed to the paper's figures. The paper's justification of independence for the first family ("a unique edge of length $d$ not used by any of the remaining tours") is inaccurate, since each length-$d$ edge lies in two rotations; the conclusion itself is what is stated here. For $n=4$ the count is $2$.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, pp. 20–21, proof of Theorem 5.1

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Proof of Theorem 5.1 (pp. 20–21): for `4 ∣ n` there are `n(n - 3)/2` Hamiltonian cycles on
which Inequality (2) is tight and whose incidence vectors are linearly independent. -/
theorem tight_tours (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) :
    ∃ τ : Fin (n * (n - 3) / 2) → Equiv.Perm (Fin n),
      (∀ i, circletForm n (MetricTSP.tourVec (τ i)) = (n : ℝ) - 2) ∧
        LinearIndependent ℝ (fun i => MetricTSP.tourVec (τ i)) := by sorry

end CircletTSP.Facet
