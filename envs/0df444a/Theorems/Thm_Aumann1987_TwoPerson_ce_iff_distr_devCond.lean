-- Prove2me | Theorems.Thm_Aumann1987_TwoPerson_ce_iff_distr_devCond
-- name    : Aumann1987.TwoPerson.ce_iff_distr_devCond
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:26:51.433474+00:00
-- url     : https://prove2.me/theorems/57fa5683-97b9-4210-9e7f-1c677317bb99
-- title:
--   Sect. 2 — a correlated strategy pair is a c.e. iff its distribution satisfies (2.2)
-- statement:
--   Let $S^1,S^2$ be finite action sets with payoffs $h^1,h^2:S^1\times S^2\to\mathbb R$, let $(\Gamma,\mu)$ be a finite probability space, and let $f=(f^1,f^2):\Gamma\to S^1\times S^2$ be a correlated strategy pair with distribution $p_{jk}=\mu\{f^1=j,\ f^2=k\}$. Then $f$ is a correlated equilibrium (Definition 2.1) if and only if
--
--   $$\sum_j\sum_k p_{jk}\,h^1_{\varphi(j)k}\le\sum_j\sum_k p_{jk}\,h^1_{jk}\ \ \text{for all }\varphi:S^1\to S^1,\qquad \sum_j\sum_k p_{jk}\,h^2_{j\psi(k)}\le\sum_j\sum_k p_{jk}\,h^2_{jk}\ \ \text{for all }\psi:S^2\to S^2.$$
--
--   This makes precise the paper's remark that correlated strategy $n$-tuples "can for most practical purposes be identified with their distributions": whether $f$ is an equilibrium depends on $f$ only through its distribution.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, p. 4 (PDF p. 5), Sect. 2, identification of correlated strategy n-tuples with their distributions

import Mathlib
import Definitions.Def_Aumann1987_TwoPerson_Model

open Finset

namespace Aumann1987.TwoPerson

/-- **Identification with distributions** (Aumann 1987, Sect. 2, p. 4, PDF p. 5: "Much like mixed
strategies, correlated strategy n-tuples can for most practical purposes be identified with their
distributions"). A correlated strategy pair `(f₁, f₂)` on the finite probability space `(Γ, μ)` is
a correlated equilibrium (Definition 2.1, (2.2)) if and only if its distribution `p = distr μ f₁ f₂`
satisfies both players' equilibrium conditions written on distributions.

Formalization Note: two players (the case of Proposition 2.3); deviations are `φ ∘ fⁱ`. -/
theorem ce_iff_distr_devCond {S₁ S₂ : Type*} [Fintype S₁] [Fintype S₂]
    [DecidableEq S₁] [DecidableEq S₂] (h₁ h₂ : S₁ → S₂ → ℝ)
    {Γ : Type*} [Fintype Γ] (μ : Γ → ℝ) (hμ : IsProbVec μ) (f₁ : Γ → S₁) (f₂ : Γ → S₂) :
    IsCE h₁ h₂ μ f₁ f₂ ↔
      DevCond₁ h₁ (distr μ f₁ f₂) ∧ DevCond₂ h₂ (distr μ f₁ f₂) := by sorry

end Aumann1987.TwoPerson
