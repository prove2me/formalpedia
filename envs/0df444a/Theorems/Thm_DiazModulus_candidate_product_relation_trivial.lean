-- Prove2me | Theorems.Thm_DiazModulus_candidate_product_relation_trivial
-- name    : DiazModulus.candidate_product_relation_trivial
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:39:35.483631+00:00
-- url     : https://prove2.me/theorems/43fb7a9c-c1ad-4556-80d7-3aacd4d897c9
-- title:
--   Candidates of equal modulus satisfy no non-trivial product relation: their arguments form a Sidon set
-- statement:
--   **Candidates on a circle: the arguments form a Sidon set.**
--
--   Let $u_1, u_2, u_3, u_4$ be candidates for Diaz's conjecture with $|u_1| = |u_3|$ and $u_1 u_2 = u_3 u_4$. Then
--
--   $$u_3 \in \mathbb{Q}\,u_1 \quad\text{or}\quad u_2 \in \mathbb{Q}\,u_3 \quad\text{or}\quad u_2 \in \mathbb{Q}\,\bar u_1 .$$
--
--   Read in terms of arguments: fix an algebraic radius $r$ and let $\Phi_r \subset \mathbb{R}/\pi\mathbb{Z}$ be the set of arguments of the candidates of modulus $r$. If $\varphi_1 + \varphi_2 = \varphi_3 + \varphi_4 \neq 0$ with all $\varphi_j \in \Phi_r$, then $\{\varphi_1, \varphi_2\} = \{\varphi_3, \varphi_4\}$. In particular $\Phi_r$ contains no three-term arithmetic progression. Rational multiples of modulus one are $\pm1$, and $-u$ is a candidate whenever $u$ is.
--
--   This is `DiazModulus.candidate_quotient_rigid` applied to $u_1 u_2 / u_3 = u_4$. It constrains families of candidates that are algebraically independent (`DiazModulus.log_pair_rigid_of_trdeg_one`), where the four exponentials theorem in transcendence degree one is silent. Like every exclusion in this mission it is vacuous if Diaz's conjecture holds.
--
--   **Novelty.** The statement is a short consequence of the six exponentials and Gelfond–Schneider theorems. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Corollary 6.11, in the algebraic form its proof uses. Novelty is not asserted. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi). Background: the six exponentials theorem (Lang, Ramachandra) and the Gelfond-Schneider theorem (1934).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_product_relation_trivial (u₁ u₂ u₃ u₄ : ℂ) (h₁ : IsCandidate u₁)
    (h₂ : IsCandidate u₂) (h₃ : IsCandidate u₃) (h₄ : IsCandidate u₄)
    (hmod : u₁ * conj u₁ = u₃ * conj u₃) (hrel : u₁ * u₂ = u₃ * u₄) :
    (∃ r : ℚ, u₃ = (r : ℂ) * u₁) ∨ (∃ r : ℚ, u₂ = (r : ℂ) * u₃) ∨
      (∃ r : ℚ, u₂ = (r : ℂ) * conj u₁) := by sorry

end DiazModulus
