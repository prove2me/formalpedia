-- Prove2me | Theorems.Thm_EqualSubsetSum_Faster_lemma_C_1
-- name    : EqualSubsetSum.Faster.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:22:12.3292+00:00
-- url     : https://prove2.me/theorems/7a20f379-9f71-4938-a346-2eeec3fdc44e
-- title:
--   Lemma C.1 — stability of the color domains under parameter perturbation
-- statement:
--   Let $K\subseteq[0,1]^N$ be compact and convex. For parameters $a$ in a fixed set, put $D_a=\{x\in K: L(a,x)\le0\text{ for every }L\in\mathcal L\}$, where $\mathcal L$ is a finite set of functions, each affine in $x$ and satisfying $|L(a,x)-L(a',x)|\le c_1\|a-a'\|_\infty$ for all $x\in K$. Suppose a common point $x_\star\in K$ satisfies $L(a,x_\star)\le-c_2$ for every parameter $a$ and every $L\in\mathcal L$, where $c_2>0$. Then for every $x\in D_a$ there is $x'\in D_{a'}$ with
--   $$\|x-x'\|_\infty\le\frac{c_1}{c_2}\|a-a'\|_\infty ,$$
--   and the same holds with $a$ and $a'$ exchanged.
--
--   Differences from the source:
--   - encoding: parameters a in a fixed set, compared in ‖·‖∞ → a set Par ⊆ ℝ^M (Fin M → ℝ with Mathlib's sup norm); reason: the source's ‖a − a'‖∞ is the sup norm of a real parameter vector
--   - encoding: a finite set 𝓛 of functions, each affine in x → a family L : ι → (ℝ^M → ℝ^N → ℝ) over a finite index type, with L l a an affine map ℝ^N → ℝ for every parameter a ∈ Par; reason: a finite set of functions indexed by a Fintype
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 55, Lemma C.1

import Mathlib

namespace EqualSubsetSum.Faster

/-- Lemma C.1 (p. 55). `K ⊆ [0,1]^N` compact and convex; for parameters `a` in a fixed set `Par`,
`D_a = {x ∈ K : L(a, x) ≤ 0 for every L ∈ 𝓛}` with `𝓛` finite, each `L(a, ·)` affine and
`|L(a, x) - L(a', x)| ≤ c₁ ‖a - a'‖∞` on `K`; a common `x★ ∈ K` has `L(a, x★) ≤ -c₂ < 0` for
every parameter and every `L`. Then every `x ∈ D_a` has some `x' ∈ D_{a'}` with
`‖x - x'‖∞ ≤ (c₁/c₂) ‖a - a'‖∞` (and the same with `a`, `a'` exchanged). Norms on
`Fin N → ℝ` and `Fin M → ℝ` are Mathlib's sup norms. -/
theorem lemma_C_1 {N M : ℕ} {ι : Type} [Fintype ι]
    (K : Set (Fin N → ℝ)) (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (hK01 : K ⊆ Set.Icc (0 : Fin N → ℝ) 1)
    (Par : Set (Fin M → ℝ)) (L : ι → (Fin M → ℝ) → (Fin N → ℝ) → ℝ)
    (hAff : ∀ l, ∀ a ∈ Par, ∃ f : (Fin N → ℝ) →ᵃ[ℝ] ℝ, ∀ x, L l a x = f x)
    (c₁ c₂ : ℝ)
    (hLip : ∀ l, ∀ a ∈ Par, ∀ a' ∈ Par, ∀ x ∈ K, |L l a x - L l a' x| ≤ c₁ * ‖a - a'‖)
    (hc₂ : 0 < c₂) (xStar : Fin N → ℝ) (hxStar : xStar ∈ K)
    (hStar : ∀ a ∈ Par, ∀ l, L l a xStar ≤ -c₂) :
    (∀ a ∈ Par, ∀ a' ∈ Par, ∀ x ∈ K, (∀ l, L l a x ≤ 0) →
        ∃ x' ∈ K, (∀ l, L l a' x' ≤ 0) ∧ ‖x - x'‖ ≤ (c₁ / c₂) * ‖a - a'‖) ∧
    (∀ a ∈ Par, ∀ a' ∈ Par, ∀ x ∈ K, (∀ l, L l a' x ≤ 0) →
        ∃ x' ∈ K, (∀ l, L l a x' ≤ 0) ∧ ‖x - x'‖ ≤ (c₁ / c₂) * ‖a - a'‖) := by sorry

end EqualSubsetSum.Faster
