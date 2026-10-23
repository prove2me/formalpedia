-- Prove2me | Theorems.Thm_CircletTSP_Facet_claim_4_2
-- name    : CircletTSP.Facet.claim_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:07.066743+00:00
-- url     : https://prove2.me/theorems/5d4730c0-bd7c-4b5a-9168-2decea0993b4
-- title:
--   Claim 4.2, p. 13 — rotation moves a structure A or B2 to u = 1 at equal circlet cost
-- statement:
--   Let $n$ be a positive multiple of $4$ and $H$ a Hamiltonian cycle on $K_n$. If $H$ contains structure A (resp. B2) of Figure 4 at some vertex $u$, then there is a Hamiltonian cycle $H'$ with the same value of $\sum_{i=1}^{d} c_i t_i$ containing structure A (resp. B2) at $u=1$.
--
--   Hence a counterexample to Theorem 3.1 with an instance of A or B2 may be assumed to have it at $u=1$, which is Claim 4.2 ("without loss of generality, we may assume that $u=1$").
--
--   **Formalization Note** Stated in the form the proof gives (relabelling $i\mapsto i-(u-1)$ preserves every length), which implies the printed claim about counterexamples. The paper's vertex $1$ is the 0-based vertex $0$.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 13, Claim 4.2 and its proof

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Claim 4.2 (p. 13), in the form its proof gives: a Hamiltonian cycle containing structure A
(resp. B2) of Figure 4 at some `u` can be relabelled into one of the same circlet cost containing
the same structure at `u = 1` (the vertex `0` in 0-based labels). -/
theorem claim_4_2 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n)) (u : Fin n) :
    (IsStructA π u → ∃ π' : Equiv.Perm (Fin n),
      circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
        IsStructA π' ⟨0, hn⟩) ∧
    (IsStructB2 π u → ∃ π' : Equiv.Perm (Fin n),
      circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
        IsStructB2 π' ⟨0, hn⟩) := by sorry

end CircletTSP.Facet
