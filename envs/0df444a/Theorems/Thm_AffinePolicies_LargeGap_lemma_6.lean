-- Prove2me | Theorems.Thm_AffinePolicies_LargeGap_lemma_6
-- name    : AffinePolicies.LargeGap.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:09:03.818885+00:00
-- url     : https://prove2.me/theorems/5308b6b4-122b-4a7e-81a9-9d0614e5b520
-- title:
--   Lemma 6, PDF p. 19 — the permuted instance ℐ(σ) of (22) equals ℐ
-- statement:
--   Let $m\in\mathbb N$, $\delta\in\mathbb R$, and let $(c,d,A,B,\mathcal U)$ be the instance (19). For a permutation $\sigma$ of $\{1,\dots,m\}$ the permuted instance $\mathcal I(\sigma)$ of (22) has data
--   $$c'=c^\sigma,\quad d'=d^\sigma,\quad A'=A^\sigma,\quad B'=B^\sigma,\quad \mathcal U'=\mathcal U^\sigma=\{b^\sigma : b\in\mathcal U\},$$
--   where $x^\sigma_j=x_{\sigma(j)}$ and $M^\sigma_{ij}=M_{\sigma(i),\sigma(j)}$. The lemma states that $\mathcal I(\sigma)=\mathcal I$ for every $\sigma\in S^m$:
--   $$c^\sigma=c,\quad d^\sigma=d,\quad A^\sigma=A,\quad B^\sigma=B,\quad \mathcal U^\sigma=\mathcal U .$$
--
--   Together with Lemma 7 this shows that permuting an optimal affine solution yields another optimal affine solution.
--
--   **Formalization Note** The paper writes $c'=0$ and $A'=0$; these are $c^\sigma$ and $A^\sigma$ since $c=0$, $A=0$, and are included as conjuncts. No threshold on $m$ is needed.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, (22) and Lemma 6, PDF p. 19

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

namespace AffinePolicies.LargeGap

theorem lemma_6 (δ : ℝ) (m : ℕ) :
    ∀ σ : Equiv.Perm (Fin m),
      c19 m ∘ σ = c19 m ∧ d19 m ∘ σ = d19 m ∧ (A19 m).submatrix σ σ = A19 m ∧
        (B19 m δ).submatrix σ σ = B19 m δ ∧ (fun b => b ∘ σ) '' U19 m δ = U19 m δ := by sorry

end AffinePolicies.LargeGap
