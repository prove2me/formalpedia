-- Prove2me | Theorems.Thm_CookPvsNP_NP_ne_coNP
-- name    : CookPvsNP.NP_ne_coNP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T14:34:33.869229+00:00
-- url     : https://prove2.me/theorems/a9fd68cc-3d48-4e38-a904-b24006afa84d
-- title:
--   NP $\neq$ coNP
-- statement:
--   The conjecture that NP is not closed under complement. Over the binary alphabet,
--   $$\mathrm{NP}_{\{0,1\}}\neq\mathrm{coNP}_{\{0,1\}}.$$
--
--   This is open and stronger than the goal: since P is closed under complement, $\mathrm P=\mathrm{NP}$ would give $\mathrm{NP}=\mathrm{coNP}$. Cook notes that it is equivalent to the assertion that no formal proof system for tautologies has polynomial-size proofs of all tautologies.
-- source:
--   S. Cook, The P versus NP Problem, official Clay Mathematics Institute problem description, https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf, §2, pp. 5–6 ("The conjecture NP ≠ coNP ..."); Formal Conjectures (Google DeepMind), FormalConjectures/Millennium/PvsNP.lean, https://github.com/google-deepmind/formal-conjectures (theorem NP_ne_coNP)

import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- The conjecture `NP ≠ coNP` (Cook §2), for languages over the binary alphabet. -/
theorem NP_ne_coNP : NP Bool ≠ coNP Bool := by sorry

end CookPvsNP
