-- Prove2me | Theorems.Thm_CommonAgencyVCG_Algorithmic_lemma_2
-- name    : CommonAgencyVCG.Algorithmic.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:33.446034+00:00
-- url     : https://prove2.me/theorems/0d1fb4b2-4da2-42ec-be4a-e2b6f0598e95
-- title:
--   Lemma 2, p. 18 — an LL, IR IIVCG contract exists iff k_{a*(b)} ≤ Σ_ℓ m^ℓ(b) for all b ∈ V
-- statement:
--   This is the necessary and sufficient condition for an IIVCG contract with both participation guarantees.
--
--   Fix a common agency setting satisfying the standing assumptions. There exists an IIVCG contract that satisfies limited liability and individual rationality if and only if
--   $$k_{a^*(b)} \le \sum_{\ell\in[n]} m^\ell(b) \qquad \forall b\in\mathcal V.$$
--
--   The condition involves only the setting, so it reduces the existence question to checking an inequality between two quantities that are each the value of a linear program.
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, p. 18, Lemma 2

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

/-- Lemma 2, p. 18 (necessary and sufficient condition): an IIVCG contract that is LL and IR
exists iff `k_{a*(b)} ≤ ∑_ℓ m^ℓ(b)` for all `b ∈ V`. -/
theorem lemma_2 (S : Setting n A O) (hS : S.Standing) :
    (∃ t : Contract n O, IsIIVCG S t ∧ IsLL S t ∧ IsIR S t) ↔
      ∀ b, InDom S b → kCost S (aStar S b) ≤ ∑ ℓ, mBound S ℓ b := by sorry

end CommonAgencyVCG.Algorithmic
