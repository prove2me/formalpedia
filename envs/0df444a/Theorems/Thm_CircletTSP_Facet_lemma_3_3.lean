-- Prove2me | Theorems.Thm_CircletTSP_Facet_lemma_3_3
-- name    : CircletTSP.Facet.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:09.498041+00:00
-- url     : https://prove2.me/theorems/93555103-1e6f-427c-b073-ffb1fca5de14
-- title:
--   Lemma 3.3, pp. 9–10 — a tour violating Inequality (2) has t₁ + 2t_d > n + 2
-- statement:
--   Let $n$ be a positive multiple of $4$ and $d=n/2$. Let $H$ be a Hamiltonian cycle on $K_n$ with incidence vector $x=\chi_H$ such that
--   $$\sum_{i=1}^{d} c_i t_i < n-2 .$$
--   Then
--   $$t_1+2t_d > n+2 .$$
--
--   A counterexample to validity must therefore use many cheap edges, those of length $1$ and $d$. By Theorem 3.1 no Hamiltonian cycle satisfies the hypothesis; the lemma is a step of the paper's minimal-counterexample proof and is stated exactly as printed.
--
--   **Formalization Note** "A valid TSP instance" is read as a Hamiltonian cycle, given by an ordering `π`; $0<n$ is added (the paper's $n=2d$ with $d$ even is tacitly positive).
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, pp. 9–10, Lemma 3.3

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Lemma 3.3 (pp. 9–10): a Hamiltonian cycle violating Inequality (2) satisfies
`t₁ + 2 t_d > n + 2`, where `d = n / 2`. -/
theorem lemma_3_3 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n))
    (hlt : circletForm n (MetricTSP.tourVec π) < (n : ℝ) - 2) :
    lenCount n 1 (MetricTSP.tourVec π) + 2 * lenCount n (n / 2) (MetricTSP.tourVec π) >
      (n : ℝ) + 2 := by sorry

end CircletTSP.Facet
