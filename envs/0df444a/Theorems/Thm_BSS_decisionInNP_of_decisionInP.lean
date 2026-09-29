-- Prove2me | Theorems.Thm_BSS_decisionInNP_of_decisionInP
-- name    : BSS.decisionInNP_of_decisionInP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T15:08:27.048431+00:00
-- url     : https://prove2.me/theorems/3afc9b30-652d-4d00-bb36-ab1f1970d199
-- title:
--   §5 Prop. 2: $P \subseteq NP$ over $\mathbb{R}$
-- statement:
--   Proposition 2 of §5 (p. 25): $NP \supseteq P$ over $\mathbb{R}$. The proof is to run the machine
--   witnessing membership in $P$ and ignore the guess.
--
--   Formally, a decision problem whose yes-instances are contained in its instance space and which
--   lies in $P$ over $\mathbb{R}$ also lies in $NP$ over $\mathbb{R}$. The containment hypothesis is
--   needed: clause (c) of the definition of $NP$ quantifies over $Y_{\mathrm{yes}}$, and a witness for
--   $y$ can only be produced from the behaviour of the $P$-machine at admissible inputs.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §5, p. 25, Proposition 2

import Definitions.Def_BSSFeasibility

namespace BSS

theorem decisionInNP_of_decisionInP (Y Yyes : Set (Rinf ℝ)) (hsub : Yyes ⊆ Y)
    (hP : DecisionInP Y Yyes) : DecisionInNP Y Yyes := by sorry

end BSS
