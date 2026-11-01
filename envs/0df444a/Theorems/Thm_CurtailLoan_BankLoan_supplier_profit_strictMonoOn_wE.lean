-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_supplier_profit_strictMonoOn_wE
-- name    : CurtailLoan.BankLoan.supplier_profit_strictMonoOn_wE
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T13:45:03.031917+00:00
-- url     : https://prove2.me/theorems/ef2ecc00-8982-43b6-b661-4d6336dc9976
-- title:
--   $w^E$ on p. 8 (PDF 8) — the unconstrained supplier profit $(w-c)\bar F^{-1}(w)$ strictly increases on $(0, w^E]$
-- statement:
--   Consider a regular demand law (a probability law with density $f$ vanishing on $(-\infty,0)$, continuous and positive on the positive open support, finite mean, IGFR), and a unit cost $0<c<1$. Let $\bar F^{-1}(w)=\inf\{Q\ge 0:\bar F(Q)\le w\}$ and let $w^E$ be the root in $(0,1]$ of
--   $$w\bigl[1-\bar F^{-1}(w)\,h(\bar F^{-1}(w))\bigr]=c,$$
--   taken as the smallest $w\in(0,1]$ at which the left side reaches $c$ (here $h=f/\bar F$ is the failure rate). Then the supplier's profit without capital constraint
--   $$\Pi_S(w)=(w-c)\,\bar F^{-1}(w)$$
--   is strictly increasing on $(0,w^E]$.
--
--   This is the defining property of the supplier's unconstrained optimal price $w^E$ on p. 8 (the Lariviere–Porteus wholesale-price model): with $Q=\bar F^{-1}(w)$ one has $dQ/dw=-1/f(Q)$, so
--   $$\frac{d\Pi_S}{dw}=\frac{c-w[1-Q\,h(Q)]}{f(Q)},$$
--   which is positive for $w<w^E$. It is the monotonicity used, in the case where the insured loan limit does not bind at $w^t_2$, in the proof of Proposition 2 (2), Appendix p. 30 (where $\Pi^{I*}_S=(w^t_2-c)\bar F^{-1}(w^t_2)$ and $w^t_2\le w^E$).
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), p. 8 (PDF 8), definition of w^E as the root of w[1 - F̄^{-1}(w) h(F̄^{-1}(w))] = c (supplier's optimal price without capital constraint); used in the proof of Proposition 2 (2), Appendix p. 30 (PDF 63)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

theorem supplier_profit_strictMonoOn_wE (P : Params) (hR : P.Regular)
    (hc0 : 0 < P.c) (hc1 : P.c < 1) :
    StrictMonoOn (fun w => (w - P.c) * Finv P w) (Set.Ioc 0 (wE P)) := by sorry

end CurtailLoan.BankLoan
