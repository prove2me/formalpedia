-- Prove2me | Theorems.Thm_ArtShortage_CashSubsidy_proposition_1
-- name    : ArtShortage.CashSubsidy.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:43.811223+00:00
-- url     : https://prove2.me/theorems/0952f673-da7a-460b-8d6f-a992d8d9557a
-- title:
--   Proposition 1, p. 10 — no intervention: (q∗1, p∗1) = (1/2 − g/8, 1/2 + g/8), (q∗2, p∗2) = (1/2, 1/2 + g/4 + g²/16)
-- statement:
--   Consider the no-intervention trader with budget adjustment factor $0<g<4$ (and $1+g<\lambda$). The trader's total revenue is
--   $$R(q_1,q_2)=q_1(1-q_1)+\big(1+g(1-q_1)\big)q_2(1-q_2),\qquad (q_1,q_2)\in[0,1]^2 .$$
--   It has the unique maximizer
--   $$(q_1^*,q_2^*)=\Big(\tfrac12-\tfrac g8,\ \tfrac12\Big).$$
--   The corresponding prices are
--   $$p_1^*=1-q_1^*=\tfrac12+\tfrac g8,\qquad p_2^*=(1-q_2^*)\big(1+g(1-q_1^*)\big)=\tfrac12+\tfrac g4+\tfrac{g^2}{16}.$$
--
--   This is the benchmark $q^1_\phi=1/2-g/8$ against which Proposition 3 compares the cash-subsidy equilibrium.
--
--   **Formalization Note** "The optimal quantity" is stated as an equality of sets: the set of maximizers over $[0,1]^2$ is exactly the singleton. The standing assumption $1+g<\lambda$ is carried for uniformity but is not used.
-- source:
--   Levi, Singhvi & Zheng, Artificial Shortage in Agricultural Supply Chains, SSRN 3332493 (version of 2021-04-14; MSOM forthcoming), p. 10, Proposition 1

import Mathlib
import Definitions.Def_ArtShortage_CashSubsidy_Model

namespace ArtShortage.CashSubsidy

theorem proposition_1 (g lam : ℝ) (hS : Standing g lam) :
    {x : ℝ × ℝ | IsNoIntOpt g x.1 x.2} = {(1/2 - g/8, 1/2)} ∧
      p1 (1/2 - g/8) = 1/2 + g/8 ∧
      p2NoInt g (1/2 - g/8) (1/2) = 1/2 + g/4 + g^2/16 := by sorry

end ArtShortage.CashSubsidy
