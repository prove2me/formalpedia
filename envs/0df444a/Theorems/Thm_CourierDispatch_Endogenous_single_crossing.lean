-- Prove2me | Theorems.Thm_CourierDispatch_Endogenous_single_crossing
-- name    : CourierDispatch.Endogenous.single_crossing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:57.836242+00:00
-- url     : https://prove2.me/theorems/d93253ec-f5b1-4b7f-9306-e5c39cab949b
-- title:
--   (A.7) — the unique crossing of optimal revenues
-- statement:
--   For each $C_B\in[0.58,0.59]$, let $G_{C_B}(\alpha)$ be the batch optimal revenue minus the dedicated optimal revenue at wait cost $\alpha$ and radius one. For every $c,r>0$, the revenue gap scales as
--   $$
--   r\,[\operatorname{Opt}_B(C_B,c,r)-\operatorname{Opt}_D(c,r)]=G_{C_B}(cr).
--   $$
--   There is one $\alpha^*>0$ with $G_{C_B}(\alpha^*)=0$: $G_{C_B}$ is positive for $0<\alpha<\alpha^*$ and negative for $\alpha>\alpha^*$. The paper reports $\alpha^*\approx0.1355$ at $C_B=0.583$.
--
--   This single crossing gives the common threshold in the product $cr$ used by Propositions 3 and 4.
--
--   **Formalization Note** The Lean name `lam` denotes $\lambda$. $G$ is defined through the suprema in (A.3). The printed closed form (A.7) inherits the erroneous coefficient from (A.6). The paper writes $G(\alpha)\le0$ for $\alpha\ge\alpha^*$; strict negativity above the unique zero expresses its stated single-crossing conclusion. The bracket for $C_B$ extends the printed numerical substitution.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), Online Appendix p. 3, proof of Proposition 3, (A.7) (corrected as documented in paper.md)

import Mathlib
import Definitions.Def_CourierDispatch_Endogenous_Setting

namespace CourierDispatch.Endogenous

theorem single_crossing (CB : ℝ) (hCB : CourierDispatch.Exogenous.CBRange CB) :
    (∀ c r : ℝ, 0 < c → 0 < r →
      r * (OptB CB c r - OptD c r) = G CB (c * r)) ∧
    ∃ αs : ℝ, 0 < αs ∧ G CB αs = 0 ∧
      (∀ α : ℝ, 0 < α → α < αs → 0 < G CB α) ∧
      (∀ α : ℝ, αs < α → G CB α < 0) := by sorry

end CourierDispatch.Endogenous
