-- Prove2me | Theorems.Thm_ComputationalLearning_phi_closed_form
-- name    : ComputationalLearning.phi_closed_form
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:13:19.087371+00:00
-- url     : https://prove2.me/theorems/0089d1bc-a1f1-4edf-8868-1862f23c8c6c
-- title:
--   Lemma 3.2: Φ_d(m) = ∑_{i=0}^{d} (m choose i)
-- statement:
--   **Lemma 3.2.** $\Phi_d(m) = \sum_{i=0}^{d} \binom{m}{i}$.
--
--   Formally: for all natural numbers $d, m$, the function of Definition 11 equals $\sum_{i=0}^{d}\binom{m}{i}$.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §3.4 p. 56, Lemma 3.2

import Definitions.Def_ComputationalLearning_VC

open MeasureTheory

namespace ComputationalLearning

/-- **Lemma 3.2** (p. 56): `Φ_d(m) = ∑_{i=0}^{d} (m choose i)`. -/
theorem phi_closed_form (d m : ℕ) :
    Phi d m = ∑ i ∈ Finset.range (d + 1), m.choose i := by sorry

end ComputationalLearning
