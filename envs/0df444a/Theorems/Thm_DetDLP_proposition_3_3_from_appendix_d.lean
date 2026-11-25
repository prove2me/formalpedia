-- Prove2me | Theorems.Thm_DetDLP_proposition_3_3_from_appendix_d
-- name    : DetDLP.proposition_3_3_from_appendix_d
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T09:06:43.704587+00:00
-- url     : https://prove2.me/theorems/fdad421a-7024-41f4-a5d9-efb9c75aa029
-- title:
--   Proposition 3.3: Deterministic Primitive Root Modulo $p$ in Time $2^{O(b/(\log b)^{1/4})}$ (under Appendix D.4)
-- statement:
--   Assume the two contraction interfaces of OpenAI Appendix D.4 (`OpenAIAppendixDPremise`). Then there exist a deterministic multitape Turing machine $M$ and a constant $C \in \mathbb{N}$ such that for every prime $p \ge 2$ (with $b = \lceil \log_2 p \rceil$), there is a unit $h \in (\mathbb{Z}/p\mathbb{Z})^\times$ of exact multiplicative order $p - 1$ whose canonical binary representative is output by $M$ on input $p$ within time and space
--
--   $$2^{C b / (\log_{\mathrm{safe}} b)^{1/4}}.$$
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Section 3.3, Proposition 3.3 (p. 14); conditional on OpenAI (Oct 25, 2026), Appendix D, Section D.4.

import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem proposition_3_3_from_appendix_d (hOAI : OpenAIAppendixDPremise) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ h : (ZMod p)ˣ,
          orderOf h = p - 1 ∧
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C (bitLen p)) (mainSpaceBound C (bitLen p)) := by sorry

end DetDLP
