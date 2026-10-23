-- Prove2me | Theorems.Thm_DisclosureDiscretion_InfoSystem_proposition_7_ab
-- name    : DisclosureDiscretion.InfoSystem.proposition_7_ab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:48.859455+00:00
-- url     : https://prove2.me/theorems/e8428a3c-36bb-4e08-88a7-455ec70fd5c8
-- title:
--   Proposition 7(a)–(b), p. 24 (PDF 26) — expected stock price under N and under P
-- statement:
--   Assume the standing assumptions $0<t<1$, $k>0$, $0<p<1$, $\bar c>k/[t(1-t)]$. The CEO's ex ante payoff under no information system is
--   $$E[\wp(N,s)]=\begin{cases}[1-t]\bar c/2 & k<t\bar c/2,\\ \bar c/2 & k\ge t\bar c/2,\end{cases}$$
--   and under the public system $P$ it is
--   $$E[\wp(P,s)]=\begin{cases}\dfrac{[1-t]t\bar c^2+pk^2}{2t\bar c} & k<t\bar c/2,\\[2mm] \dfrac{[1-pt]t\bar c^2+pk^2}{2t\bar c} & k\ge t\bar c/2.\end{cases}$$
--
--   These are the two benchmarks against which discretionary disclosure is compared.
--
--   **Formalization Note** $E[\wp(P,s)]$ is defined in the model as $(1-p)E[\wp(N,s)]+p\int_0^{\bar c}V(c)\,dc/\bar c$, with $V$ the price after a published $c$; part (b) evaluates this integral.
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), p. 24 (PDF 26), Proposition 7(a)–(b)

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

namespace DisclosureDiscretion.InfoSystem

theorem proposition_7_ab (cbar t p k : ℝ) (h : Standing cbar t p k) :
    (k < t * cbar / 2 → expPriceN cbar t k = (1 - t) * cbar / 2) ∧
    (t * cbar / 2 ≤ k → expPriceN cbar t k = cbar / 2) ∧
    (k < t * cbar / 2 →
      expPriceP cbar t p k = ((1 - t) * t * cbar ^ 2 + p * k ^ 2) / (2 * t * cbar)) ∧
    (t * cbar / 2 ≤ k →
      expPriceP cbar t p k = ((1 - p * t) * t * cbar ^ 2 + p * k ^ 2) / (2 * t * cbar)) := by sorry

end DisclosureDiscretion.InfoSystem
