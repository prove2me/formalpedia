-- Prove2me | Theorems.Thm_BernoulliPoA_lemma_EC_1
-- name    : BernoulliPoA.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:40.882965+00:00
-- url     : https://prove2.me/theorems/541f9605-17ae-40e9-b133-045163e1dced
-- title:
--   Lemma EC.1, p.ec1 — $\gamma_{\mathsf{pr}}(\mathcal C,q)=\inf_{\omega\ge1}\Psi(\omega)$
-- statement:
--   Let $\mathcal C$ be a family of nonnegative nondecreasing costs and $q\in(0,1]$.
--
--   1. If $c(k)=0$ for some $c\in\mathcal C\setminus\{c_0\}$ and some $k\ge1$, no pair $(\lambda,\mu)$ satisfies (28), and $\gamma_{\mathsf{pr}}(\mathcal C,q)=\infty$.
--   2. If $c(k)>0$ for all $c\in\mathcal C\setminus\{c_0\}$ and all $k\ge 1$, then
--   $$
--   \gamma_{\mathsf{pr}}(\mathcal C,q)=\inf_{\omega\ge1}\Psi(\omega).
--   $$
--
--   This dual form of the smoothness bound is what the tightness argument works with.
--
--   Differences from the source:
--   - encoding: one identity γpr(C,q) = inf_{ω≥1} Ψ(ω), both sides ∞ when c(k) = 0 for some c ≠ c0, k ≥ 1 ((EC.3) divides by c(k) = 0) → two clauses: in the degenerate case the parameter set is empty and γpr = ⊤; otherwise the identity in ℝ≥0∞; reason: a real quotient c^q(1+k)/(q c(k)) cannot be +∞; the clauses are the two cases of the paper's proof and together cover every C
--   - generalization: c : ℕ → [0,∞) nondecreasing → c : ℕ → ℝ nonnegative and nondecreasing on the loads k ≥ 1, c(0) free; reason: no quantity reads c(0), and every family of the source satisfies this condition
--   - encoding: c ∈ C \ {c0} → c is nonzero at some load k ≥ 1; reason: c(0) is free in the Lean family
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Lemma EC.1 and its proof, p.ec1

import Mathlib
import Definitions.Def_BernoulliPoA_IsCostClass
import Definitions.Def_BernoulliPoA_prophetSmoothParams
import Definitions.Def_BernoulliPoA_gammaPr
import Definitions.Def_BernoulliPoA_Psi
open scoped ENNReal

namespace BernoulliPoA

/-- **Lemma EC.1.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Lemma EC.1 and its proof, p.ec1: `γ_pr(C, q) = inf_{ω ≥ 1} Ψ(ω)`.

**Formalization Note** The two clauses are the two cases of the paper's proof. (a) If `c(k) = 0` for some `c ∈ C \ {c₀}` and `k ≥ 1`, no pair satisfies (28) and `γ_pr = ∞`; in this case
the paper's `Ψ` is `∞` by the division by `c(k) = 0` of (EC.3), which a real quotient cannot express. (b) Otherwise every quotient in `β` is meaningful and (EC.2) holds in `ℝ≥0∞`.
Together the clauses cover every family `C`. -/
theorem lemma_EC_1 {C : Set (ℕ → ℝ)} (hC : IsCostClass C) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ((∃ c ∈ C, (∃ j, 1 ≤ j ∧ c j ≠ 0) ∧ ∃ k, 1 ≤ k ∧ c k = 0) →
      prophetSmoothParams C q = ∅ ∧ gammaPr C q = ⊤) ∧
    ((∀ c ∈ C, (∃ j, 1 ≤ j ∧ c j ≠ 0) → ∀ k, 1 ≤ k → 0 < c k) →
      gammaPr C q = ⨅ ω ∈ Set.Ici (1 : ℝ), Psi C q ω) := by sorry

end BernoulliPoA
