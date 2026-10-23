-- Prove2me | Theorems.Thm_CircletTSP_Facet_claim_4_1
-- name    : CircletTSP.Facet.claim_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:07.385452+00:00
-- url     : https://prove2.me/theorems/87aa7e19-bcfe-4684-ad77-cdd28f806dc2
-- title:
--   Claim 4.1, p. 13 — reflection exchanges structures B1 and B2 at equal circlet cost
-- statement:
--   Let $n$ be a positive multiple of $4$. Then:
--
--   1. for every Hamiltonian cycle $H$ on $K_n$ containing structure B2 (Figure 4) at some vertex, there is a Hamiltonian cycle $H'$ with the same value of $\sum_{i=1}^{d} c_i t_i$ containing structure B1 at some vertex;
--   2. conversely, every Hamiltonian cycle containing B1 at some vertex has a counterpart of the same circlet value containing B2.
--
--   In particular, a counterexample to Theorem 3.1 on $n$ vertices containing an instance of B2 yields a counterexample on $n$ vertices containing an instance of B1, and vice versa, which is Claim 4.1. It reduces Lemma 3.4 to the structures A and B2.
--
--   **Formalization Note** The paper's claim is about counterexamples, which do not exist once Theorem 3.1 is proved; it is stated here in the stronger form its proof gives (relabelling $i\mapsto n-i$ preserves every length), which implies the printed claim. Both directions are posed: the claim prints B2 ⇒ B1, the proof says "and vice versa", and the reduction uses B1 ⇒ B2.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 13, Claim 4.1 and its proof

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Claim 4.1 (p. 13), in the form its proof gives: relabelling vertex `i` as `n - i` turns a
Hamiltonian cycle containing structure B2 of Figure 4 into one of the same circlet cost containing
structure B1, and vice versa. In particular a counterexample to Theorem 3.1 with a B2 yields one
with a B1. -/
theorem claim_4_1 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) :
    (∀ (π : Equiv.Perm (Fin n)) (u : Fin n), IsStructB2 π u →
      ∃ (π' : Equiv.Perm (Fin n)) (u' : Fin n),
        circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
          IsStructB1 π' u') ∧
    (∀ (π : Equiv.Perm (Fin n)) (u : Fin n), IsStructB1 π u →
      ∃ (π' : Equiv.Perm (Fin n)) (u' : Fin n),
        circletForm n (MetricTSP.tourVec π') = circletForm n (MetricTSP.tourVec π) ∧
          IsStructB2 π' u') := by sorry

end CircletTSP.Facet
