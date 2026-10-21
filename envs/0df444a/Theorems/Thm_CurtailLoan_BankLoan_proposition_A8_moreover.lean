-- Prove2me | Theorems.Thm_CurtailLoan_BankLoan_proposition_A8_moreover
-- name    : CurtailLoan.BankLoan.proposition_A8_moreover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:19.715982+00:00
-- url     : https://prove2.me/theorems/8b93afea-bb86-46a3-a222-b80441477d78
-- title:
--   Proposition A.8 Moreover, Appendix p. 23 (PDF 56) — $w^t_2$ decreases with $l, u, t$, increases with $\tau$, independent of $c$
-- statement:
--   Consider the model of the mission with a regular demand law. For each parameter, consider a segment on which the standing assumptions and $t < t_k(w_{min})$ hold at every point, all other parameters fixed. Then the larger root $w^t_2$ of $t_k(w) = t$ satisfies:
--
--   1. it strictly decreases with the initial capital $l$, the initial loan limit $u$ and the fixed insurance premium $t$;
--   2. it strictly increases with the fixed bank fee $\tau$;
--   3. it does not depend on the supplier's unit cost $c$.
--
--   Since $w^t_2$ is the equilibrium price in Area II, these are the comparative statics of the equilibrium price that drive Proposition 2.
--
--   **Formalization Note** Item 3 holds by construction ($t_k$ does not involve $c$). The later clauses of the paragraph (the dependence of $w^t_2$ on $v$, and the monotonicity of $t_0(w_I)$, $t_k(w_{II})$, $t_0(w^a_2)$, $t_0(w^E)$, $t_k(w_s)$) are not formalized.
-- source:
--   Wang & Cai, Curtailing bank loan and loan insurance under risk regulations in supply chain finance, SSRN 3760840 (forthcoming Management Science 2023; PDF of 2023-02-24), Appendix p. 23 (PDF 56), Proposition A.8, Moreover, first clause

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

namespace CurtailLoan.BankLoan

/-- Proposition A.8, "Moreover", first clause, Appendix p. 23 (PDF 56): `w^t_2` strictly decreases
with `l`, `u` and `t`, strictly increases with `τ`, and is independent of `c`. -/
theorem proposition_A8_moreover (P : Params) (hR : P.Regular) :
    (∀ l₁ l₂ : ℝ, l₁ < l₂ →
      (∀ x ∈ Set.Icc l₁ l₂, Standing (P.withL x) ∧
        (P.withL x).t < tk (P.withL x) (wmin (P.withL x))) →
      wt2 (P.withL l₂) < wt2 (P.withL l₁)) ∧
    (∀ u₁ u₂ : ℝ, u₁ < u₂ →
      (∀ x ∈ Set.Icc u₁ u₂, Standing (P.withU x) ∧
        (P.withU x).t < tk (P.withU x) (wmin (P.withU x))) →
      wt2 (P.withU u₂) < wt2 (P.withU u₁)) ∧
    (∀ t₁ t₂ : ℝ, t₁ < t₂ →
      (∀ x ∈ Set.Icc t₁ t₂, Standing (P.withT x) ∧
        (P.withT x).t < tk (P.withT x) (wmin (P.withT x))) →
      wt2 (P.withT t₂) < wt2 (P.withT t₁)) ∧
    (∀ τ₁ τ₂ : ℝ, τ₁ < τ₂ →
      (∀ x ∈ Set.Icc τ₁ τ₂, Standing (P.withTau x) ∧
        (P.withTau x).t < tk (P.withTau x) (wmin (P.withTau x))) →
      wt2 (P.withTau τ₁) < wt2 (P.withTau τ₂)) ∧
    (∀ c₁ c₂ : ℝ, wt2 (P.withC c₁) = wt2 (P.withC c₂)) := by sorry

end CurtailLoan.BankLoan
