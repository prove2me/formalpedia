-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_lemma_1
-- name    : ExtremalForrelation.Nonadaptive.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:40.475553+00:00
-- url     : https://prove2.me/theorems/969bc2bb-5803-489b-8253-4c0fb9f281fc
-- title:
--   Lemma 1 — coset pairings and exact counts
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Let $K$ be a subspace of $\mathbb F_2^n$ with $\dim K=m$, and let $K^\perp$ be its orthogonal complement for the binary pairing.
--
--   1. For $u\in K$ and a coset $D$ of $K^\perp$, the value $\langle u,y\rangle$ is the same for every $y\in D$; call it $\langle u,D\rangle$.
--   2. For distinct cosets $D\ne D'$ of $K^\perp$ and a basis $u_1,\dots,u_m$ of $K$, $\langle u_\ell,D\rangle\ne\langle u_\ell,D'\rangle$ for some $1\le\ell\le m$.
--   3. For linearly independent $u_1,\dots,u_t\in K$ and bits $b_1,\dots,b_t$, exactly
--   $$\frac{M}{2^t}$$
--   of the $M$ cosets $D$ of $K^\perp$ satisfy $\langle u_\ell,D\rangle=b_\ell$ for all $1\le\ell\le t$.
--
--   The same three statements hold with $K$ and $K^\perp$ interchanged.
--
--   These facts identify cosets of $K^\perp$ with their bit patterns against a basis of $K$; they compute the neighbourhoods of the pinning graph in Claim 1.
--
--   Differences from the source:
--   - encoding: a basis u_1, …, u_m of K (resp. of K^⊥) → m linearly independent vectors lying in K (resp. orth K); reason: dim K = m (and dim K^⊥ = m), so these are exactly the bases
--   - encoding: ⟨u, D⟩ = b_ℓ for the common value ⟨u, D⟩ → ⟨u, y⟩ = b_ℓ for every y in D; reason: by clause 1 the two readings agree; the count is stated as a real equality with M/2^t
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Lemma 1, p. 8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Lemma 1 (p. 8). For a subspace `K` of `𝔽₂ⁿ` with `dim K = m = n/2`:
(1) for `u ∈ K`, `⟨u, y⟩` is the same for every `y` in a coset `D` of `K^⊥`;
(2) for distinct cosets `D ≠ D₁` of `K^⊥` and a basis `u_1, …, u_m` of `K`,
`⟨u_ℓ, D⟩ ≠ ⟨u_ℓ, D₁⟩` for some `ℓ`;
(3) for linearly independent `u_1, …, u_t ∈ K` and bits `b_1, …, b_t`, exactly `M/2^t` of the
`M` cosets `D` of `K^⊥` satisfy `⟨u_ℓ, D⟩ = b_ℓ` for all `ℓ`;
and the same three statements with `K` and `K^⊥` interchanged. A basis of an
`m`-dimensional space is given as `m` linearly independent vectors in it. -/
theorem lemma_1 {n : ℕ} (hn : 4 ∣ n) (K : Submodule (ZMod 2) (V n))
    (hK : Module.finrank (ZMod 2) K = n / 2) :
    -- (1)
    (∀ u ∈ K, ∀ D : V n ⧸ orth K, ∀ y₁ y₂ : V n,
      Submodule.Quotient.mk y₁ = D → Submodule.Quotient.mk y₂ = D → dot u y₁ = dot u y₂) ∧
    -- (2)
    (∀ D₁ D₂ : V n ⧸ orth K, D₁ ≠ D₂ → ∀ u : Fin (n / 2) → V n, (∀ ℓ, u ℓ ∈ K) →
      LinearIndependent (ZMod 2) u →
      ∃ ℓ, ∀ y₁ y₂ : V n, Submodule.Quotient.mk y₁ = D₁ → Submodule.Quotient.mk y₂ = D₂ →
        dot (u ℓ) y₁ ≠ dot (u ℓ) y₂) ∧
    -- (3)
    (∀ (t : ℕ) (u : Fin t → V n), (∀ ℓ, u ℓ ∈ K) → LinearIndependent (ZMod 2) u →
      ∀ b : Fin t → ZMod 2,
      ((Finset.univ.filter (fun D : V n ⧸ orth K =>
          ∀ ℓ, ∀ y : V n, Submodule.Quotient.mk y = D → dot (u ℓ) y = b ℓ)).card : ℝ) =
        (2 : ℝ) ^ (n / 2) / 2 ^ t) ∧
    -- (1) with `K` and `K^⊥` interchanged
    (∀ u ∈ orth K, ∀ C : V n ⧸ K, ∀ x₁ x₂ : V n,
      Submodule.Quotient.mk x₁ = C → Submodule.Quotient.mk x₂ = C → dot u x₁ = dot u x₂) ∧
    -- (2) with `K` and `K^⊥` interchanged
    (∀ C₁ C₂ : V n ⧸ K, C₁ ≠ C₂ → ∀ u : Fin (n / 2) → V n, (∀ ℓ, u ℓ ∈ orth K) →
      LinearIndependent (ZMod 2) u →
      ∃ ℓ, ∀ x₁ x₂ : V n, Submodule.Quotient.mk x₁ = C₁ → Submodule.Quotient.mk x₂ = C₂ →
        dot (u ℓ) x₁ ≠ dot (u ℓ) x₂) ∧
    -- (3) with `K` and `K^⊥` interchanged
    (∀ (t : ℕ) (u : Fin t → V n), (∀ ℓ, u ℓ ∈ orth K) → LinearIndependent (ZMod 2) u →
      ∀ b : Fin t → ZMod 2,
      ((Finset.univ.filter (fun C : V n ⧸ K =>
          ∀ ℓ, ∀ x : V n, Submodule.Quotient.mk x = C → dot (u ℓ) x = b ℓ)).card : ℝ) =
        (2 : ℝ) ^ (n / 2) / 2 ^ t) := by sorry

end ExtremalForrelation.Nonadaptive
