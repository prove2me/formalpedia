-- Prove2me | Theorems.Thm_FermiGaussMix_lemma_B_4
-- name    : FermiGaussMix.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:14.262926+00:00
-- url     : https://prove2.me/theorems/fe961328-954b-4cdc-b891-85780d2015bb
-- title:
--   Lemma B.4 — one label removal keeps the form $(\mathbf 1+\alpha\Gamma)\sigma$, the bound $\alpha\le 2^{-m}$ and nonnegativity
-- statement:
--   Let $C=(\mathbf 1+\alpha\Gamma)\sigma$ have the form (B.23)–(B.24) relative to $S$. When $\alpha>0$, let $m=|\operatorname{supp}\Gamma\cap S|$ and assume $m>0$, $\alpha\le 2^{-m}$. Choose $i\in\operatorname{supp}\Gamma\cap S$ when $\alpha>0$ and any $i\in S$ when $\alpha=0$, set $S'=S\setminus\{i\}$, and take $p_1=\frac12$, $p_2=\dots=p_7=\frac1{12}$.
--
--   For every realization of $Z_1,Z_2$ with $r\le\frac1{12}$ and every $k$, the operator $C_k=(\mathbf 1+H_k)\sigma$ has the form (B.23)–(B.24) relative to $S'$: one has $H_k=\alpha_k\Gamma_k$ with $\alpha_k\ge 0$ and a Hermitian even monomial $\Gamma_k$ disjoint from the pairs of $\sigma$, with $m_k=|\operatorname{supp}\Gamma_k\cap S'|$ and
--   $$
--   \alpha_k\le 2^{-m_k},
--   $$
--   and $C_k$ is nonnegative. This is the inductive step behind Proposition B.3.
--
--   Differences from the source:
--   - generalization: realizations of Z_1, Z_2 drawn through (B.33) from M − 1 and M† − 1 → every Z_1, Z_2 equal to 0 or of the shape (B.46), with a common 0 ≤ r ≤ 1/12; reason: every realization of (B.33) has this shape, and no property of M is used beyond it
--   - reading: R_j in (B.46), with no parity stated → R_j even; reason: the Z_j come from the expansion of M − 1, and M is even, as Lemma B.2 and p. 12 ("preserves fermion parity") say
--   - encoding: "If H_k is nonzero, write H_k = α_kΓ_k"; if H_k = 0, C_k = σ → one existential: H_k = α_k ε_k P_{R_k}, with α_k = 0 and R_k = ∅ when H_k = 0; reason: the same case split; at H_k = 0 (B.45) is trivial
--   - encoding: "No condition on Γ is needed when α = 0" → the form (B.23) is still a hypothesis at α = 0, with (B.43) required only for α > 0; reason: at α = 0 neither T_k nor C sees Γ, and Γ = 1 satisfies the form, so nothing is excluded
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, Lemma B.4, p. 16, with eqs. (B.38)–(B.40), p. 15

import Mathlib
import Definitions.Def_FermiGaussMix_IsMiddleForm

open scoped BigOperators ComplexOrder
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Lemma B.4, p.16** (Han, Zhao, Liu, arXiv:2609.35159v1). Let `C = (1 + αΓ)σ` have the form (B.23)–(B.24) relative to
`S`, with `Γ = ε P_{R₀}`. When `α > 0`, let `m = |supp Γ ∩ S|` and assume `m > 0`, `α ≤ 2^{-m}`, and choose
`i ∈ supp Γ ∩ S`; when `α = 0`, choose any `i ∈ S`. Set `S' = S \ {i}` and `p = (1/2, 1/12, …, 1/12)`. For every realization
of `Z₁, Z₂` and every `k`, the operator `C_k = (1 + H_k)σ` has the form (B.23)–(B.24) relative to `S'`: `H_k = α_k Γ_k` with
`α_k ≥ 0`, `Γ_k = ε_k P_{R_k}` and `α_k ≤ 2^{-m_k}`, where `m_k = |supp Γ_k ∩ S'|`; and `C_k` is nonnegative.

**Formalization Note** `Z₁, Z₂` range over every operator of the shape (B.46) with a common `0 ≤ r ≤ 1/12`, which covers
every realization of (B.33). The case `H_k = 0` of the page is `α_k = 0`, with `R_k = ∅`. "No condition on `Γ` is needed when
`α = 0`" concerns (B.43): at `α = 0` the hypotheses and the `T_k` do not see `Γ` beyond the form (B.23), which `Γ = 1` always
satisfies. -/
theorem lemma_B_4 {n : ℕ} {S : Finset (Fin (2 * n))} {α ε c r : ℝ} {R₀ : Finset (Fin (2 * n))}
    {M : List (Fin (2 * n) × Fin (2 * n))} {s : Fin (2 * n) × Fin (2 * n) → ℝ} {i : Fin (2 * n)}
    {Z₁ Z₂ : Op n}
    (hform : IsMiddleForm S α ε R₀ c M s)
    (hα : 0 < α → 0 < (R₀ ∩ S).card ∧ α ≤ (1 / 2 : ℝ) ^ (R₀ ∩ S).card ∧ i ∈ R₀ ∩ S)
    (hi : i ∈ S)
    (hr₀ : 0 ≤ r) (hr : r ≤ 1 / 12)
    (hZ₁ : IsZRealization S r Z₁) (hZ₂ : IsZRealization S r Z₂) (k : Fin 7) :
    ∃ (αk εk : ℝ) (Rk : Finset (Fin (2 * n))),
      IsMiddleForm (S.erase i) αk εk Rk c M s ∧
      hOp α ε R₀ Z₁ Z₂ k = ((αk : ℂ) * (εk : ℂ)) • P n Rk ∧
      αk ≤ (1 / 2 : ℝ) ^ (Rk ∩ S.erase i).card ∧
      (((1 : Op n) + hOp α ε R₀ Z₁ Z₂ k) * sigmaOp c M s).PosSemidef := by sorry

end FermiGaussMix
