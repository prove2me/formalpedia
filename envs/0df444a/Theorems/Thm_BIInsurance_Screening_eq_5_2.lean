-- Prove2me | Theorems.Thm_BIInsurance_Screening_eq_5_2
-- name    : BIInsurance.Screening.eq_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:44:36.373751+00:00
-- url     : https://prove2.me/theorems/854d9c76-2725-4ebe-a3b9-09700fc703f3
-- title:
--   Eq. (5.2)–(5.4), pp. 17–18 — (IR-L) and (IC-HL) are redundant; at an optimal menu (IC-LH), (IR-H) bind, y_H = g_H(s_H), y_L = g_L(s_H, s_L)
-- statement:
--   Assume the standing assumptions. For menus $(y_H,s_H,y_L,s_L)$ of the insurer's problem (5.1):
--   1. (IR-L) is redundant: if $s_H,s_L\in[0,\bar s]$, then (IC-LH) and (IR-H) imply (IR-L);
--   2. (IC-HL) is redundant once (IC-LH) binds: if $s_H,s_L\in[0,\bar s]$, $s_H\le s_L$ and $E_{\delta,Z}[\pi^I_L(K,y_L,s_L)]=E_{\delta,Z}[\pi^I_L(K,y_H,s_H)]$, then (IC-HL) holds;
--   3. at every optimal menu of (5.1), (IC-LH) and (IR-H) bind,
--
--   $$
--   -y_L+E_{\delta,Z}[\pi^I_L(K,s_L)]=-y_H+E_{\delta,Z}[\pi^I_L(K,s_H)],\qquad -y_H+E_{\delta,Z}[\pi^I_H(K,s_H)]=E_{\delta,Z}[\pi^N_H(K)],
--   $$
--
--   and hence $y_H=g_H(s_H)$ and $y_L=g_L(s_H,s_L)$ with $g_H,g_L$ from (5.3)–(5.4).
--
--   This reduces the insurer's problem to a problem in the coverages alone, with objective $R(s_H,s_L)$.
--
--   **Formalization Note** The page asserts "(IC-HL) and (IR-L) are redundant, and (IC-LH) and (IR-H) are binding" as a consequence of Proposition 2. (IC-HL) is not implied by (IC-LH) alone when (IC-LH) is slack (a very low $y_L$ violates it), so its redundancy is stated for menus where (IC-LH) binds, with $s_H\le s_L$, the configuration in which the page uses it.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), pp. 17–18, §5.1, eqs. (5.1)–(5.4)

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem eq_5_2 (P : Params) (hS : P.Standing) :
    (∀ M : Menu, M.sH ∈ Set.Icc 0 P.sbar → M.sL ∈ Set.Icc 0 P.sbar →
        IC_LH P M → IR_H P M → IR_L P M) ∧
      (∀ M : Menu, M.sH ∈ Set.Icc 0 P.sbar → M.sL ∈ Set.Icc 0 P.sbar → M.sH ≤ M.sL →
        EpiI P P.muL M.yL M.sL = EpiI P P.muL M.yH M.sH → IC_HL P M) ∧
      (∀ M : Menu, IsOptimalMenu P M →
        EpiI P P.muL M.yL M.sL = EpiI P P.muL M.yH M.sH ∧
          EpiI P P.muH M.yH M.sH = EpiN P P.muH ∧
          M.yH = gH P M.sH ∧ M.yL = gL P M.sH M.sL) := by sorry

end BIInsurance.Screening
