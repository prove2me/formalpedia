-- Prove2me | Theorems.Thm_ExplicitTensorBarrier694_Explicit_Supplement_lemma_4_1
-- name    : ExplicitTensorBarrier694.Explicit.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:39:37.482848+00:00
-- url     : https://prove2.me/theorems/d7471a5b-4d59-45e1-98e2-65035b568b1f
-- title:
--   Lemma 4.1 — normalization of a linear flattening
-- statement:
--   Let $L:(\mathbb C^n)^{\otimes3}\to\mathrm{Mat}_{u,v}(\mathbb C)$ be a nonzero linear map, and set $r=\max_T\operatorname{rank}L(T)$ and $\rho=\rho(L)=\max_{x,y,z}\operatorname{rank}L(x\otimes y\otimes z)$. Then there are matrices $M_{ijk}\in\mathrm{Mat}_r(\mathbb C)$, $i,j,k\in\{1,\dots,n\}$, with
--
--   $$\sum_{ijk}M_{ijk}M_{ijk}^\dagger=\sum_{ijk}M_{ijk}^\dagger M_{ijk}=I_r$$
--
--   and
--
--   $$\operatorname{rank}\Big(\sum_{ijk}x_iy_jz_kM_{ijk}\Big)\le\rho\qquad\text{for all }x,y,z\in\mathbb C^n.$$
--
--   This normalization is the first step of the proof of the upper bound $\Pi(n)\le2n-2+\frac2{n+1}$ in Theorem 1.2. No complex conjugation is applied to $x,y,z$. This is a paper-proved result awaiting a formal proof.
--
--   Differences from the source:
--   - encoding: (ℂⁿ)^{⊗3} and pure tensors x ⊗ y ⊗ z → coordinate arrays Tensor n n n = Fin n → Fin n → Fin n → ℂ (published), pure x y z with entries x_i y_j z_k; reason: the standard basis identifies the two spaces; ranks and linear maps are transported unchanged
--   - encoding: u, v positive integers → u v : ℕ, with L ≠ 0; reason: a nonzero linear map into Mat_{u,v} forces u, v ≥ 1, so u = 0 or v = 0 adds no instance
-- source:
--   Benjamin Lovitz, STOC 2027 submission #694 (October 2026), Lemma 4.1, p.11 (PDF p.11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/694.pdf

import Mathlib
import Definitions.Def_ExplicitTensorBarrier694_Explicit_Supplement_Flattening

open scoped BigOperators Matrix

namespace ExplicitTensorBarrier694.Explicit.Supplement

open ExplicitTensorBarrier694.Explicit

/-- Lovitz, STOC 2027 submission #694 (October 2026), Lemma 4.1, p.11. For every nonzero
linear flattening L : (ℂⁿ)^{⊗3} → Mat_{u,v}(ℂ), with r = max_T rank L(T) and ρ = ρ(L),
there are r × r matrices M_{ijk} with Σ M M† = Σ M† M = I_r and
rank(Σ x_i y_j z_k M_{ijk}) ≤ ρ for all x, y, z ∈ ℂⁿ. -/
theorem lemma_4_1 (n u v : ℕ) (L : Tensor n n n →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ)
    (hL : L ≠ 0) :
    ∃ M : Fin n → Fin n → Fin n →
        Matrix (Fin (flatMaxRank (⇑L))) (Fin (flatMaxRank (⇑L))) ℂ,
      (∑ i, ∑ j, ∑ k, M i j k * (M i j k)ᴴ) = 1 ∧
      (∑ i, ∑ j, ∑ k, (M i j k)ᴴ * M i j k) = 1 ∧
      ∀ x y z : Fin n → ℂ, (coeffMatrix M x y z).rank ≤ flatRho (⇑L) := by sorry

end ExplicitTensorBarrier694.Explicit.Supplement
