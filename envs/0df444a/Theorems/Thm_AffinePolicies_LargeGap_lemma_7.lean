-- Prove2me | Theorems.Thm_AffinePolicies_LargeGap_lemma_7
-- name    : AffinePolicies.LargeGap.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:09:01.919212+00:00
-- url     : https://prove2.me/theorems/00203b60-f940-4dfc-9ce4-302450f46926
-- title:
--   Lemma 7, PDF p. 19 — permuting an optimal affine solution, y^σ(b) = P^σ b + q^σ, keeps it optimal
-- statement:
--   Let $m\in\mathbb N$, $\delta\in\mathbb R$, and consider the instance (19). Let $(x,\,y)$ with $y(b)=Pb+q$ be an optimal affine solution, and let $\sigma$ be a permutation of $\{1,\dots,m\}$. Define
--   $$P^\sigma_{ij}=P_{\sigma(i),\sigma(j)},\qquad q^\sigma_j=q_{\sigma(j)}\qquad(i,j=1,\dots,m).$$
--   Then $(x,\,y^\sigma)$ with
--   $$y^\sigma(b)=P^\sigma b+q^\sigma$$
--   is also an optimal affine solution of the same instance. Note that $y^\sigma(b)$ is not the vector $y(b)$ with its coordinates permuted.
--
--   This is the step that makes the set of optimal affine solutions closed under the action of $S^m$; averaging over that action (Lemma 8) produces a symmetric optimum.
--
--   **Formalization Note** The page writes $\sigma\in S^n$; the symmetric group meant is $S^m$ (the indices run over $1,\dots,m$). The first-stage decision $x$ is kept unchanged; since $A=0$ and $c=0$ it plays no role. Optimality is with respect to the worst-case cost over $\mathcal U$ among all feasible affine solutions. No threshold on $m$ is needed.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, Lemma 7, PDF p. 19

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

namespace AffinePolicies.LargeGap

theorem lemma_7 (δ : ℝ) (m : ℕ) (σ : Equiv.Perm (Fin m)) (x : Fin m → ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ)
    (hopt : AffinePolicies.Simplex.IsOptimalAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) x P q) :
    AffinePolicies.Simplex.IsOptimalAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) x
      (P.submatrix σ σ) (q ∘ σ) := by sorry

end AffinePolicies.LargeGap
