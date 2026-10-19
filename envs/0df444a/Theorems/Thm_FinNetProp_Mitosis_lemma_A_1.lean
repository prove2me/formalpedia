-- Prove2me | Theorems.Thm_FinNetProp_Mitosis_lemma_A_1
-- name    : FinNetProp.Mitosis.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:31.65401+00:00
-- url     : https://prove2.me/theorems/ebcb0a3a-3496-46a6-a5ca-197dbc914aa4
-- title:
--   Lemma A.1, p. 2809 — under impartiality and invariance to mitosis, payments to rationally commensurable liabilities are proportional
-- statement:
--   Let $F = (N, z, L)$ be a financial network, let $i, j, k \in N$, and let $q, r$ be positive integers with
--   $$L_{ij} = \frac{q}{r}\, L_{ik}.$$
--   Let $b$ be a bankruptcy rule satisfying impartiality (Axiom 3.5) and invariance to mitosis (Axiom 4.1). Then
--   $$b_{ij}(F) = \frac{q}{r}\, b_{ik}(F).$$
--
--   This is the key step of Part (II) of the proof of Theorem 4.2: together, impartiality and mitosis force an agent's payments to be proportional to its liabilities whenever these are rational multiples of one another.
--
--   **Formalization Note** The page writes $q, r \in \mathbb N$; here $q \ge 1$ and $r \ge 1$ are required, matching the page's proof (it splits $j$ into $q$ and $k$ into $r$ identical agents, and $q/r$ needs $r \ne 0$) and its lead-in sentence ("one liability of an agent is a positive rational multiple of another liability"). No distinctness of $i, j, k$ is assumed, as on the page.
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, p. 2809, Lemma A.1

import Mathlib
import Definitions.Def_FinNetProp_Mitosis_Setting

namespace FinNetProp.Mitosis

theorem lemma_A_1 (b : BankruptcyRule) (himp : Impartial b) (hmit : InvariantToMitosis b)
    (F : FinNet) (i j k : ℕ) (hi : i ∈ F.N) (hj : j ∈ F.N) (hk : k ∈ F.N) (q r : ℕ)
    (hq : 0 < q) (hr : 0 < r) (hL : F.L i j = ((q : ℝ) / (r : ℝ)) * F.L i k) :
    b F i j = ((q : ℝ) / (r : ℝ)) * b F i k := by sorry

end FinNetProp.Mitosis
