-- Prove2me | Theorems.Thm_BundledExpansion_SeqSim_lemma_1
-- name    : BundledExpansion.SeqSim.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:07.401901+00:00
-- url     : https://prove2.me/theorems/05bf705b-0e59-41de-a7cb-fe0f91c0630c
-- title:
--   Lemma 1, p. 12 — sequential cycle costs
-- statement:
--   In a feasible sequential cycle $[s,e]$, cluster $l$ is purchased at $m\ge1$ leading expansions, followed by one purchase of the other type $f$. Write $\tau_k$ for its replenishment times, $w_l=\sum_i h_i a_{il}$, $F_i(s,e)=\int_s^e D_i(s,t)\,dt$, and $\alpha=a_{11}a_{22}-a_{12}a_{21}$. The three cost terms are
--
--   $$
--   A(m+1),\qquad \frac{(c_1a_{22}-c_2a_{21})D_1(s,e)+(c_2a_{11}-c_1a_{12})D_2(s,e)}{\alpha},
--   $$
--   $$
--   \sum_{k=1}^{m}(\tau_{k+1}-\tau_k)\frac{w_lD_f(s,\tau_{k+1})}{a_{fl}}+\psi,
--   \quad \psi=\sum_i h_i[(e-\tau_{m+1})D_i(s,e)-F_i(s,e)].
--   $$
--
--   The purchase term is independent of the number of leading expansions, and $\psi$ is independent of that number once the final split time is fixed. **Formalization Note** A valid cycle lies within the horizon and has positive determinant; the paper’s Assumption 1 is imposed on its leading intervals. Lean indices 0 and 1 represent the paper’s 1 and 2.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, p. 12 (PDF 13), Lemma 1, equations (3)–(4)

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim

theorem lemma_1 (P : Params) (hS : P.Standing) (hR : P.Regular)
    (C : SeqCycle) (hC : C.Valid P) :
    C.fixed P = P.A * (C.m + 1) ∧
    purchase P (C.plan P) = commonPurchase P C.start C.stop ∧
    holding P (C.plan P) C.start C.stop =
      (∑ k ∈ Finset.range C.m,
        (C.τ (k + 1) - C.τ k) * w P C.lead *
          D P C.follow C.start (C.τ (k + 1)) / P.a C.follow C.lead) +
        psi P C := by sorry

end BundledExpansion.SeqSim
