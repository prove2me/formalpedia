-- Prove2me | Theorems.Thm_CommonOwnership_Governance_lemma1_last_step
-- name    : CommonOwnership.Governance.lemma1_last_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:49.829877+00:00
-- url     : https://prove2.me/theorems/6b5e2d33-5dc1-44e3-8ee8-dd3b60c7c0db
-- title:
--   Lemma 1, p. 13, last step of its proof, p. 38 (PDF p. 41) — ∂Π*/∂s ≥ 0, zero exactly at s = 0 and s = β
-- statement:
--   Let $0<\theta\le1$ and $0<\beta\le1$, and let $\lambda(s)$ be the common-ownership weight (17). Let industry profit be a function $P$ of $\lambda$ that is differentiable at every $\lambda\in[0,1]$ with derivative $P'(\lambda)$, where
--   $$P'(\lambda)\ge0\ \text{ for } \lambda\in[0,1],\qquad P'(\lambda)>0\ \text{ for } \lambda\in[0,1).$$
--   Then for every $s\in[0,\beta]$ the industry profit $\Pi^*(s)=P(\lambda(s))$ is differentiable at $s$, and its derivative $d=\partial\Pi^*/\partial s$ satisfies
--   $$d\ge0,\qquad d=0\iff s=0\ \text{or}\ s=\beta .$$
--
--   This is the conclusion of Lemma 1: industry profits increase with the degree of common ownership, strictly for $0<s<\beta$, with a zero derivative at $s=0$ and $s=\beta$. It is the step of the proof that combines the sign of $\partial\Pi^*/\partial\lambda$ with the sign of $\partial\lambda/\partial s$.
--
--   **Formalization Note** The sign of $\partial\Pi^*/\partial\lambda$ is a hypothesis here, not a conclusion: the paper derives it from the product-market first- and second-order conditions (8)–(9) by a computation that is not posed in this mission. Only the last step of the proof of Lemma 1 is stated.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), p. 13 (PDF p. 16), Lemma 1; Appendix A, proof of Lemma 1, last step, p. 38 (PDF p. 41)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- Lemma 1 (p. 13), last step of its proof (Appendix A, p. 38): if industry profit `P` is
differentiable in `λ` on `[0, 1]` with `∂Π*/∂λ ≥ 0`, strictly for `λ < 1`, then
`s ↦ P(λ(s))` has a nonnegative derivative on `[0, β]`, zero exactly at `s = 0` and `s = β`. -/
theorem lemma1_last_step (θ β : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (P P' : ℝ → ℝ) (hPd : ∀ l ∈ Set.Icc (0:ℝ) 1, HasDerivAt P (P' l) l)
    (hP'nn : ∀ l ∈ Set.Icc (0:ℝ) 1, 0 ≤ P' l) (hP'pos : ∀ l ∈ Set.Ico (0:ℝ) 1, 0 < P' l) :
    ∀ s ∈ Set.Icc (0:ℝ) β, ∃ d : ℝ,
      HasDerivAt (fun x => P (lam θ β x)) d s ∧ 0 ≤ d ∧ (d = 0 ↔ s = 0 ∨ s = β) := by sorry

end CommonOwnership.Governance
