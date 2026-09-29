-- Prove2me | Theorems.Thm_CookPvsNP_P_eq_NP_iff_binary
-- name    : CookPvsNP.P_eq_NP_iff_binary
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T13:46:04.270356+00:00
-- url     : https://prove2.me/theorems/7e2cd442-1134-4497-9841-2904c11d880c
-- title:
--   The P = NP question does not depend on the alphabet ($|\Sigma|\ge 2$)
-- statement:
--   Let $\Sigma$ be a finite alphabet with at least two symbols. Then
--   $$\mathrm P_\Sigma=\mathrm{NP}_\Sigma\iff\mathrm P_{\{0,1\}}=\mathrm{NP}_{\{0,1\}}.$$
--
--   This is Cook's remark that the P versus NP question does not depend on the size of the alphabet, provided it has at least two letters. It justifies stating the goal over the binary alphabet.
-- source:
--   S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §1, p. 2 ("the answer is independent of the size of the alphabet Σ (we assume |Σ| ≥ 2)")

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- Cook §1: the answer to `P = NP?` does not depend on the alphabet, as long as it has at least
two symbols. -/
theorem P_eq_NP_iff_binary (Sym : Type) [Fintype Sym] (hSym : 2 ≤ Fintype.card Sym) :
    P Sym = NP Sym ↔ P Bool = NP Bool := by sorry

end CookPvsNP
