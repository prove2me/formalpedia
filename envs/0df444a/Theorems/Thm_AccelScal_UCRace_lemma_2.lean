-- Prove2me | Theorems.Thm_AccelScal_UCRace_lemma_2
-- name    : AccelScal.UCRace.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:02.292064+00:00
-- url     : https://prove2.me/theorems/80b5a699-dab1-44d6-9af7-d5fe7076f602
-- title:
--   Lemma 2, p. 7 — project values in a race of two unconstrained firms
-- statement:
--   Let two unconstrained firms with the stated power-form technologies invest at positive intensities $R_1,R_2$ and discount at rate $r>0$. Their independent exponential discovery times have rates $\lambda_1(R_1)$ and $\lambda_2(R_2)$. Each firm pays its investment rate until the first discovery and receives its own expected project payoff only if it discovers first. The expected discounted project values are
--
--   $$
--   V_1=\frac{u_1(R_1)\lambda_1(R_1)-R_1}{r+\lambda_1(R_1)+\lambda_2(R_2)},\qquad
--   V_2=\frac{u_2(R_2)\lambda_2(R_2)-R_2}{r+\lambda_1(R_1)+\lambda_2(R_2)}.
--   $$
--
--   This identity turns the stochastic payoff in (8) into the project-value expression (9) used to analyze best responses.
--
--   **Formalization Note** The theorem gives the pointwise identities at every positive intensity pair; the paper displays the corresponding project values. The random payoff is represented by its independent mean $u_i(R_i)$.
-- source:
--   Lin, Accelerability vs. Scalability: R&D Investment Under Financial Constraints and Competition, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4503, p. 7, Lemma 2, (9)

import Mathlib
import Definitions.Def_AccelScal_UCRace_Setting

noncomputable section

namespace AccelScal.UCRace

/-- Lin, Lemma 2 and equation (9), p. 7, with the random discovery times
integrated against their independent exponential joint law. -/
theorem lemma_2 (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) (R1 R2 : ℝ) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    payoff1 T1 T2 r R1 R2 = V1 T1 T2 r R1 R2 ∧
      payoff2 T1 T2 r R1 R2 =
        (T2.u R2 * T2.lam R2 - R2) / (r + T1.lam R1 + T2.lam R2) := by sorry

end AccelScal.UCRace
