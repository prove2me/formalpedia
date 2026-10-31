-- Prove2me | Theorems.Thm_DPDeconstructed_lemma_6_2
-- name    : DPDeconstructed.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:46:31.128261+00:00
-- url     : https://prove2.me/theorems/9be82b07-cb3e-4e33-b821-35b7b92c6e74
-- title:
--   Lemma 6.2 — a unique fixed point of $F_i$ maps to the unique fixed point of $F_{i+1}$
-- statement:
--   With $E_0,E_1,E_2$, $\tau_0,\tau_1,\tau_2$, $F_0=\tau_2\tau_1\tau_0$ and $F_1=\tau_0\tau_2\tau_1$ as in Lemma 6.1: if $F_0$ has a unique fixed point $\varrho_0$ in $E_0$, then $\tau_0\varrho_0$ is the unique fixed point of $F_1$ in $E_1$.
--
--   This transfers existence and uniqueness of fixed points around the cycle; it gives Proposition 2.3 with $(E_0,E_1,E_2)=(\mathcal V,\mathcal G,\mathcal H)$ and $\tau_2=M_\sigma$.
--
--   Differences from the source:
--   - encoding: for some i in {0, 1, 2} (indices mod 3) → i = 0, for an arbitrary triple (E₀, E₁, E₂, τ₀, τ₁, τ₂); reason: the case i is the case 0 for the rotated triple, so the two statements are equivalent
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §6.1, p.26, Lemma 6.2

import Mathlib

namespace DPDeconstructed

/-- Lemma 6.2, Ma and Stachurski, *Dynamic Programming Deconstructed*, arXiv:1811.01940v2,
§6.1, p.26. With `E_i`, `τ_i`, `F₀ := τ₂ τ₁ τ₀` and `F₁ := τ₀ τ₂ τ₁` as in §6.1 (p.25): if `F₀`
has a unique fixed point `ϱ₀` in `E₀`, then `τ₀ ϱ₀` is the unique fixed point of `F₁` in `E₁`.

**Formalization Note** The paper states the lemma "for some `i` in `{0, 1, 2}`" with indices
mod 3; the case `i` is the case `i = 0` for the rotated triple, so the statement for `i = 0`
and an arbitrary triple is equivalent. -/
theorem lemma_6_2 {E₀ E₁ E₂ : Type*} [Nonempty E₀] [Nonempty E₁] [Nonempty E₂]
    (τ₀ : E₀ → E₁) (τ₁ : E₁ → E₂) (τ₂ : E₂ → E₀) (ϱ₀ : E₀)
    (hfix : (τ₂ ∘ τ₁ ∘ τ₀) ϱ₀ = ϱ₀) (huniq : ∀ e : E₀, (τ₂ ∘ τ₁ ∘ τ₀) e = e → e = ϱ₀) :
    (τ₀ ∘ τ₂ ∘ τ₁) (τ₀ ϱ₀) = τ₀ ϱ₀ ∧ ∀ f : E₁, (τ₀ ∘ τ₂ ∘ τ₁) f = f → f = τ₀ ϱ₀ := by sorry

end DPDeconstructed
