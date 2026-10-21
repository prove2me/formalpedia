-- Prove2me | Theorems.Thm_CommonAgencyVCG_Algorithmic_theorem_5
-- name    : CommonAgencyVCG.Algorithmic.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:43.588419+00:00
-- url     : https://prove2.me/theorems/b796295f-da0e-4b3c-8637-91b4b7468188
-- title:
--   Theorem 5, p. 16 — if some IIVCG contract is LL and IR, the algorithmic contract ALG1 is an LL, IR IIVCG contract
-- statement:
--   This is the main result of §4.
--
--   Fix a common agency setting satisfying the standing assumptions, and suppose that some IIVCG contract satisfies limited liability and individual rationality. Then:
--
--   1. Algorithm 1 can be run: for every bid profile $b\in\mathcal V$ there are an optimal solution $w^b$ of LP2 and an optimal solution $x^b$ of LP3 with $\sum_\ell x^b_\ell = 1$ (an admissible selection);
--   2. for every admissible selection, the contract ALG1,
--   $$\mathrm{ALG1}^\ell(b,o) = h^\ell - \big\{F_{|a^*(b)}\cdot(b^{-\ell}+x^b_\ell\,w^b) - \psi(a^*(b))\big\} + x^b_\ell\,w^b(o),$$
--   with $h^\ell$ the value of LP1, is an IIVCG contract that satisfies limited liability and individual rationality.
--
--   Since every IIVCG contract is truthful and implements the declared-welfare-maximizing action, ALG1 is a truthful, welfare-maximizing contract with both participation guarantees whenever one exists.
--
--   **Formalization Note** ALG1 is read as Algorithm 1 run with any optimal solutions of LP2 and LP3; Algorithm 1 does not specify which, so all admissible selections are quantified, and item 1 shows the quantification is not vacuous. Line 5's "Impossible" branch never fires under the hypothesis and is not modelled. The theorem's second sentence (Algorithm 1 runs in polynomial time) is a complexity claim and is not formalized. The hypothesis is read with the canonical $a^*(b)$ (welfare-maximal, then cost-maximal), the same $a^*(b)$ used in ALG1, $k$ and $m$. The standing assumptions include $n\ge 1$ (added) and convex domains (kept, unused).
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, p. 16, Theorem 5 (Definition 4; Algorithm 1, p. 20)

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

/-- Theorem 5, p. 16: in every common agency setting for which an IIVCG contract satisfying LL
and IR exists, contract ALG1 — Algorithm 1 run with any optimal solutions of LP2 and LP3 — is such a
contract (and such LP solutions exist). -/
theorem theorem_5 (S : Setting n A O) (hS : S.Standing)
    (hex : ∃ t : Contract n O, IsIIVCG S t ∧ IsLL S t ∧ IsIR S t) :
    (∃ (wsel : (Fin n → O → ℝ) → O → ℝ) (xsel : (Fin n → O → ℝ) → Fin n → ℝ),
        ValidSel S wsel xsel) ∧
      ∀ (wsel : (Fin n → O → ℝ) → O → ℝ) (xsel : (Fin n → O → ℝ) → Fin n → ℝ),
        ValidSel S wsel xsel →
          IsIIVCG S (alg1 S wsel xsel) ∧ IsLL S (alg1 S wsel xsel) ∧ IsIR S (alg1 S wsel xsel) := by sorry

end CommonAgencyVCG.Algorithmic
