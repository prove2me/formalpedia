-- Prove2me | Theorems.Thm_ApproxSyzygies_Smoothed_lemma_4_9
-- name    : ApproxSyzygies.Smoothed.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:02:56.688752+00:00
-- url     : https://prove2.me/theorems/2a504746-8477-4d60-beff-c514fa1386d3
-- title:
--   Lemma 4.9 — robust dimension and direct sum: $\{u:\nu_\lambda(M_u)\ge q\}$ lies within $\lambda(N_X/q+1)$ of a subspace of dimension $\lfloor N_X/q\rfloor$
-- statement:
--   Let $U,W$ be Euclidean spaces and $X\subseteq U\otimes W$ a subspace of dimension at most $N_X$. For $u\in U$ put $M_uw=\Pi_{X^\perp}(u\otimes w)$, $w\in W$, and let $\nu_\lambda(M_u)$ be the number of singular values of $M_u$ that are at most $\lambda$. For every integer $q\ge1$ with $\lfloor N_X/q\rfloor\le\dim U-1$ and every $\lambda\ge0$ there is a fixed subspace $U_{\mathrm{null}}\subseteq U$ with $\dim U_{\mathrm{null}}\le\lfloor N_X/q\rfloor$ such that
--   $$\{u:\nu_\lambda(M_u)\ge q\}\subseteq\Big\{u:\mathrm{dist}(u,U_{\mathrm{null}})\le\lambda\Big(\frac{N_X}{q}+1\Big)\Big\}.$$
--   It is the linear-algebra core of the one-step shrinking Lemma 4.7.
--
--   Differences from the source:
--   - encoding: Euclidean spaces $U$, $W$ and the tensor product $U\otimes W$ → $\mathbb R^{\iota}$, $\mathbb R^{\kappa}$ for finite index types and $\mathbb R^{\iota\times\kappa}$ with $(u\otimes w)_{(a,b)}=u_aw_b$ (`tens`); reason: every finite-dimensional real inner product space is isometric to some $\mathbb R^{\iota}$, and $\mathbb R^{\iota\times\kappa}$ with the Frobenius norm is the Hilbert tensor product
--   - encoding: $\nu_\lambda(M_u)$, the number of small singular values → `numSmallSV`: the number of indices $k<\dim W$ with `singularValues k ≤ λ`; reason: $M_u:W\to U\otimes W$ has $\dim W$ singular values, counted with multiplicity
--   - encoding: $\lfloor N_X/q\rfloor\le\dim(U)-1$ → `NX / q + 1 ≤ Fintype.card ι`; reason: the same condition without natural-number subtraction
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), p. 34, Lemma 4.9

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Anticoncentration

namespace ApproxSyzygies.Smoothed

/-- Lemma 4.9 (p. 34): robust dimension and direct sum. Let `U = ℝ^ι`, `W = ℝ^κ` and let
`X ⊆ U ⊗ W` have dimension at most `N_X`; put `M_u w = Π_{X^⊥}(u ⊗ w)`. For every integer
`q ≥ 1` with `⌊N_X/q⌋ ≤ dim U − 1` and every `λ ≥ 0` there is a subspace `U_null ⊆ U` of
dimension at most `⌊N_X/q⌋` such that every `u` with `ν_λ(M_u) ≥ q` satisfies
`dist(u, U_null) ≤ λ (N_X/q + 1)`. -/
theorem lemma_4_9 {ι κ : Type} [Fintype ι] [Fintype κ]
    (X : Submodule ℝ (EuclideanSpace ℝ (ι × κ))) (NX : ℕ) (hX : Module.finrank ℝ X ≤ NX)
    (q : ℕ) (hq : 1 ≤ q) (hqU : NX / q + 1 ≤ Fintype.card ι) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ Unull : Submodule ℝ (EuclideanSpace ℝ ι), Module.finrank ℝ Unull ≤ NX / q ∧
      ∀ u : EuclideanSpace ℝ ι,
        q ≤ numSmallSV
            ((Xᗮ.starProjection : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)).toLinearMap ∘ₗ
              tensLeft u) lam →
          Metric.infDist u Unull ≤ lam * ((NX : ℝ) / q + 1) := by sorry

end ApproxSyzygies.Smoothed
