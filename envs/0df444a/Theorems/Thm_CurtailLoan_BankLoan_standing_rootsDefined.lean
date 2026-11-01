-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_standing_rootsDefined
-- name    : CurtailLoan.BankLoan.standing_rootsDefined
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T13:49:01.506722+00:00
-- url     : https://prove2.me/theorems/e861c6bb-eee6-4378-a89f-5cfdd6960af9
-- title:
--   p. 9 (PDF 9) — under the standing assumptions, $u+l-\tau<\hat w\hat Q$, so the roots $w^u_1<w^u_2$ are defined
-- statement:
--   Consider the model of the mission with a regular demand law (a probability law with density $f$ that vanishes on $(-\infty,0)$, is continuous and positive on the positive open support, has finite mean, and is IGFR). Assume the standing assumptions of Propositions 1–2: the paper's global assumptions ($0<c<1$, $l\ge 0$, $t\ge 0$, $0\le\tau<u<v$, $\tau\le\tau_0(\max(w^\alpha_2,w^E))$, $l<w^EQ^E$) and
--   $$u+l-\tau<w^EQ^E,\qquad Q^E=\bar F^{-1}(w^E).$$
--   Let $\hat w$ be the (largest) maximizer of $w\bar F^{-1}(w)$ on $(0,1)$ and $\hat Q=\bar F^{-1}(\hat w)$. Then
--   $$u+l-\tau<\hat w\,\hat Q.$$
--   This is the condition under which p. 9 defines the two roots $w^u_1<w^u_2$ of $u+l-\tau=w\bar F^{-1}(w)$. It holds because $\hat w$ maximizes $w\bar F^{-1}(w)$, so $w^EQ^E\le\hat w\hat Q$. The roots $w^u_{1,2}$, and hence $t_k$, $w_{\min}$ and $w^t_2$, are therefore well defined throughout Propositions 1–2.
--
--   **Formalization note.** $\hat w$ is encoded as the supremum of the set of maximizers of $w\bar F^{-1}(w)$ on $(0,1)$. The lemma includes the fact that this maximum is attained under the regularity assumptions.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), p. 9 (PDF 9), definition of w^u_1, w^u_2 as the two roots of u + l - tau = w F̄^{-1}(w) when u + l - tau < ŵQ̂, ŵ the maximizer of w F̄^{-1}(w); with Proposition 2's preamble u + l - tau < w^E Q^E (p. 13)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

theorem standing_rootsDefined (P : Params) (hR : P.Regular) (hS : Standing P) :
    RootsDefined P := by sorry

end CurtailLoan.BankLoan
