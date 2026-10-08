-- Prove2me | Theorems.Thm_CoffmanMitrani1980_Region_lemma2_ineq_numerators
-- name    : CoffmanMitrani1980.Region.lemma2_ineq_numerators
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:16:13.729022+00:00
-- url     : https://prove2.me/theorems/c1de4ab2-4d0d-48d9-818c-257314e09d03
-- title:
--   Lemma 2, proof — second inequality, with aᵢ = ρᵢ/μᵢ
-- statement:
--   Fix the model parameters ($\lambda_i,\mu_i>0$, $\rho<1$), write $a_i=\rho_i/\mu_i$, and for a set $g$ of classes $a(g)=\sum_{i\in g}a_i$ and $\rho(g)=\sum_{i\in g}\rho_i$. Let $g_1,g_2$ be sets of classes, $g_{12}=g_1\cap g_2$, $G_{12}=g_1\cup g_2$, and suppose $h_1=g_1-g_{12}$ and $h_2=g_2-g_{12}$ are both nonempty. Then
--   $$a(g_1)(1-\rho(g_2))+a(g_2)(1-\rho(g_1))-a(g_{12})(1-\rho(G_{12}))<a(G_{12})(1-\rho(g_{12})).$$
--
--   With the first inequality, this gives the strict violation of (4) for $G_{12}$ that drives the proof of Lemma 2.
--
--   **Formalization Note.** Sums over the empty set are $0$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), DOI 10.1287/opre.28.3.810, p. 818, Lemma 2, proof: second displayed inequality after (5)

import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

namespace CoffmanMitrani1980.Region

/-- Coffman and Mitrani, Operations Research 28 (1980), p. 818 (PDF 10), Lemma 2, proof (second
inequality): with `aᵢ = ρᵢ/μᵢ`, `g₁₂ = g₁ ∩ g₂`, `G₁₂ = g₁ ∪ g₂`, and `h₁ = g₁ - g₁₂`,
`h₂ = g₂ - g₁₂` nonempty,
`(Σ_{g₁} aᵢ)(1 - Σ_{g₂} ρᵢ) + (Σ_{g₂} aᵢ)(1 - Σ_{g₁} ρᵢ) - (Σ_{g₁₂} aᵢ)(1 - Σ_{G₁₂} ρᵢ)
  < (Σ_{G₁₂} aᵢ)(1 - Σ_{g₁₂} ρᵢ)`.

**Formalization Note.** Sums over `∅` are `0`. -/
theorem lemma2_ineq_numerators {M : ℕ} (p : Params M) (g₁ g₂ : Finset (Fin M))
    (h₁ : (g₁ \ g₂).Nonempty) (h₂ : (g₂ \ g₁).Nonempty) :
    (∑ i ∈ g₁, p.a i) * (1 - ∑ i ∈ g₂, p.rho i) + (∑ i ∈ g₂, p.a i) * (1 - ∑ i ∈ g₁, p.rho i)
        - (∑ i ∈ g₁ ∩ g₂, p.a i) * (1 - ∑ i ∈ g₁ ∪ g₂, p.rho i) <
      (∑ i ∈ g₁ ∪ g₂, p.a i) * (1 - ∑ i ∈ g₁ ∩ g₂, p.rho i) := by sorry

end CoffmanMitrani1980.Region
