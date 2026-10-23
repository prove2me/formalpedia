-- Prove2me | Theorems.Thm_CircletTSP_Facet_contraction_step
-- name    : CircletTSP.Facet.contraction_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:09.941853+00:00
-- url     : https://prove2.me/theorems/b4504cb8-0582-4ce8-aa76-9c2f39d7f45d
-- title:
--   p. 17, after Proposition 4.5 — contracting a Figure 7 sequence gives a tour on n − 4 vertices at least 4 cheaper
-- statement:
--   Let $n\ge 8$ be a multiple of $4$, $d=n/2$, labels $1,\dots,n$. Let $H$ be a Hamiltonian cycle on $K_n$ that contains one of the two edge sequences of Figure 7,
--   $$\{j,1\},\{1,2\},\{2,d+2\},\{d+2,d+1\},\{d+1,k\}\quad\text{or}\quad \{j,d+2\},\{d+2,2\},\{2,1\},\{1,d+1\},\{d+1,k\},$$
--   with $j,k\notin\{1,2,d+1,d+2\}$. Let $H'$ be obtained by contraction: delete $1,2,d+1,d+2$, replace the five edges by $\{j',k'\}$, and relabel every other vertex $s$ as $s'$. Then $H'$ is a Hamiltonian cycle on $K_{n-4}$ and
--   $$\sum_{i=1}^{d-2} c'_i\, t_i(\chi_{H'})+4\ \le\ \sum_{i=1}^{d} c_i\, t_i(\chi_H).$$
--
--   By Claims 4.1 and 4.2, every structure A, B1, B2 can be brought to one of these two sequences, so this is the statement that a tour with any of the structures of Figure 4 contracts to a tour on four fewer vertices that is at least $4$ cheaper, which completes the proof of Lemma 3.4.
--
--   **Formalization Note** $n\ge 8$ is not printed in this sentence; the proof of Theorem 3.1 derives it from Claim 3.2 ("By Claim 3.2, $n\ge 8$", p. 10), and for $n=4$ there is no tour on $0$ vertices. The contracted cycle is given explicitly as the vector `contract n (tourVec π) j k` on `Fin (n - 4)` and the statement asserts that it is the incidence vector of some ordering, so the conclusion is about the specific contracted tour, not merely some cheap tour.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 17 (paragraph after Proposition 4.5) with the contraction of p. 14

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- The contraction step (p. 17, after Proposition 4.5): if a Hamiltonian cycle on `n ≥ 8`
vertices contains one of the two edge sequences of Figure 7, `{j, 1}, {1, 2}, {2, d + 2},
{d + 2, d + 1}, {d + 1, k}` or `{j, d + 2}, {d + 2, 2}, {2, 1}, {1, d + 1}, {d + 1, k}`
(1-based labels, `d = n / 2`), then contracting it (p. 14) yields a Hamiltonian cycle on
`n - 4` vertices whose circlet cost is at least `4` smaller. -/
theorem contraction_step (n : ℕ) (hn : 8 ≤ n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n)) (j k : ℕ)
    (hj : j ∈ keptLabels n) (hk : k ∈ keptLabels n) (hchain : ChainOne π j k ∨ ChainTwo π j k) :
    (∃ σ : Equiv.Perm (Fin (n - 4)),
      MetricTSP.tourVec σ = contract n (MetricTSP.tourVec π) j k) ∧
    circletForm (n - 4) (contract n (MetricTSP.tourVec π) j k) + 4 ≤
      circletForm n (MetricTSP.tourVec π) := by sorry

end CircletTSP.Facet
