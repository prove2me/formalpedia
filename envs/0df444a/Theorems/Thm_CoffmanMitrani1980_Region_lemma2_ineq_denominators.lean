-- Prove2me | Theorems.Thm_CoffmanMitrani1980_Region_lemma2_ineq_denominators
-- name    : CoffmanMitrani1980.Region.lemma2_ineq_denominators
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:16:25.329195+00:00
-- url     : https://prove2.me/theorems/1a918780-0862-477a-b0c2-125fc89ce15a
-- title:
--   Lemma 2, proof — first inequality: (1−ρ(g₁))(1−ρ(g₂)) > (1−ρ(G₁₂))(1−ρ(g₁₂))
-- statement:
--   Fix the model parameters ($\lambda_i,\mu_i>0$, $\rho<1$) and write $\rho(g)=\sum_{i\in g}\rho_i$ for a set $g$ of classes. Let $g_1,g_2$ be sets of classes, $g_{12}=g_1\cap g_2$ and $G_{12}=g_1\cup g_2$, and suppose $h_1=g_1-g_{12}$ and $h_2=g_2-g_{12}$ are both nonempty. Then
--   $$(1-\rho(g_1))(1-\rho(g_2))>(1-\rho(G_{12}))(1-\rho(g_{12})).$$
--
--   Together with the second inequality of the same proof, this shows that two tight sets of a point of $H^{**}$ cannot cross.
--
--   **Formalization Note.** Sums over the empty set are $0$, the paper's convention for $g_{12}=\emptyset$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), DOI 10.1287/opre.28.3.810, p. 818, Lemma 2, proof: first displayed inequality after (5)

import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

namespace CoffmanMitrani1980.Region

/-- Coffman and Mitrani, Operations Research 28 (1980), p. 818 (PDF 10), Lemma 2, proof (first
inequality): for sets of classes `g₁, g₂` with `h₁ = g₁ - g₁₂` and `h₂ = g₂ - g₁₂` nonempty, where
`g₁₂ = g₁ ∩ g₂` and `G₁₂ = g₁ ∪ g₂`,
`(1 - Σ_{i∈g₁} ρᵢ)(1 - Σ_{i∈g₂} ρᵢ) > (1 - Σ_{i∈G₁₂} ρᵢ)(1 - Σ_{i∈g₁₂} ρᵢ)`.

**Formalization Note.** `h₁` nonempty is `(g₁ \ g₂).Nonempty`; sums over `∅` are `0`. -/
theorem lemma2_ineq_denominators {M : ℕ} (p : Params M) (g₁ g₂ : Finset (Fin M))
    (h₁ : (g₁ \ g₂).Nonempty) (h₂ : (g₂ \ g₁).Nonempty) :
    (1 - ∑ i ∈ g₁ ∪ g₂, p.rho i) * (1 - ∑ i ∈ g₁ ∩ g₂, p.rho i) <
      (1 - ∑ i ∈ g₁, p.rho i) * (1 - ∑ i ∈ g₂, p.rho i) := by sorry

end CoffmanMitrani1980.Region
