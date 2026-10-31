-- Prove2me | Theorems.Thm_DPDeconstructed_lemma_6_1
-- name    : DPDeconstructed.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:37.19898+00:00
-- url     : https://prove2.me/theorems/7ab9280c-594e-4f57-b97e-9ba4d40ac077
-- title:
--   Lemma 6.1 — fixed points and iterates pass around the cycle $\tau_0,\tau_1,\tau_2$
-- statement:
--   Let $E_0,E_1,E_2$ be nonempty sets and $\tau_0:E_0\to E_1$, $\tau_1:E_1\to E_2$, $\tau_2:E_2\to E_0$ maps, and set
--
--   $$F_0:=\tau_2\tau_1\tau_0\ \text{ on }E_0,\qquad F_1:=\tau_0\tau_2\tau_1\ \text{ on }E_1 .$$
--
--   Then
--
--   1. if $\varrho\in E_0$ is a fixed point of $F_0$, then $\tau_0\varrho$ is a fixed point of $F_1$;
--   2. for every $n$, $F_1^n\tau_0=\tau_0F_0^n$ on $E_0$.
--
--   The lemma is the engine of the paper: with $(E_0,E_1,E_2)=(\mathbb V,\mathbb G,\mathbb H)$ and $(\tau_0,\tau_1,\tau_2)=(W_0,W_1,M)$ it converts fixed points and iterates of the Bellman operator $T=F_0$ into those of the refactored operator $S=F_1$, and back by rotating the triple.
--
--   Differences from the source:
--   - encoding: for each i = 0, 1, 2 (indices mod 3) → i = 0, for an arbitrary triple (E₀, E₁, E₂, τ₀, τ₁, τ₂); reason: the case i is the case 0 for the rotated triple (E_i, E_{i+1}, E_{i+2}, τ_i, τ_{i+1}, τ_{i+2}), so the two statements are equivalent
--   - generalization: n ∈ ℕ = {1, 2, …} (p.4) → every n : ℕ, including n = 0; reason: at n = 0 both sides are τ₀; restricting to n ≥ 1 gives the printed claim
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §6.1, p.25, Lemma 6.1 (with the definitions of E_i, τ_i, F_i and (34) of the same page)

import Mathlib

namespace DPDeconstructed

/-- Lemma 6.1, Ma and Stachurski, *Dynamic Programming Deconstructed*, arXiv:1811.01940v2,
§6.1, p.25. Let `E₀, E₁, E₂` be nonempty sets and `τ₀ : E₀ → E₁`, `τ₁ : E₁ → E₂`,
`τ₂ : E₂ → E₀`, with `F₀ := τ₂ τ₁ τ₀` on `E₀` and `F₁ := τ₀ τ₂ τ₁` on `E₁`. Then
(1) if `ϱ` is a fixed point of `F₀` in `E₀`, then `τ₀ ϱ` is a fixed point of `F₁` in `E₁`;
(2) `F₁ⁿ τ₀ = τ₀ F₀ⁿ` on `E₀` for all `n`.

**Formalization Note** The paper states the lemma "for each `i = 0, 1, 2`" with indices
mod 3. The case `i` is the case `i = 0` for the rotated triple `(E_i, E_{i+1}, E_{i+2},
τ_i, τ_{i+1}, τ_{i+2})`, so the statement for `i = 0` and an arbitrary triple is equivalent.
`n` ranges over `ℕ ∋ 0` (the paper's `ℕ` starts at `1`; `n = 0` is trivial). -/
theorem lemma_6_1 {E₀ E₁ E₂ : Type*} [Nonempty E₀] [Nonempty E₁] [Nonempty E₂]
    (τ₀ : E₀ → E₁) (τ₁ : E₁ → E₂) (τ₂ : E₂ → E₀) :
    (∀ ϱ : E₀, (τ₂ ∘ τ₁ ∘ τ₀) ϱ = ϱ → (τ₀ ∘ τ₂ ∘ τ₁) (τ₀ ϱ) = τ₀ ϱ) ∧
      ∀ n : ℕ, ∀ e : E₀, (τ₀ ∘ τ₂ ∘ τ₁)^[n] (τ₀ e) = τ₀ ((τ₂ ∘ τ₁ ∘ τ₀)^[n] e) := by sorry

end DPDeconstructed
