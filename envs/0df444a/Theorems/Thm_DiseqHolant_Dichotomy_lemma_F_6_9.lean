-- Prove2me | Theorems.Thm_DiseqHolant_Dichotomy_lemma_F_6_9
-- name    : DiseqHolant.Dichotomy.lemma_F_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:00:24.830238+00:00
-- url     : https://prove2.me/theorems/22cf9fad-a776-44c9-96f9-96db5b0163c7
-- title:
--   Lemma F.6.9 — a Möbius map permuting the $m$-th roots of unity ($m\ge3$) is $z\mapsto\alpha z$ or $z\mapsto\alpha/z$ with $\alpha^m=1$
-- statement:
--   Let $\mu_m=\{z\in\mathbb C: z^m=1\}$. A Möbius map of the Riemann sphere is written $\phi(z)=\dfrac{c+dz}{a+bz}$ with $ad-bc\neq0$.
--
--   **Lemma F.6.9.** Let $m\ge3$, and let $\phi$ have no pole on $\mu_m$ and permute $\mu_m$. Then
--   $$\phi(z)=\alpha z\quad\text{or}\quad\phi(z)=\alpha/z,\qquad\alpha\in\mu_m.$$
--
--   The lemma classifies the ratios of binary factors in the dihedral branch of the structural analysis.
--
--   **Formalization Note** "No pole on $\mu_m$" is $a+bz\neq0$ for $z\in\mu_m$, so the quotient is the true quotient there; "permute" is a bijection of $\mu_m$ onto itself. Equality of Möbius maps is stated as proportionality of coefficients: $\phi(z)=\alpha z$ means $b=c=0$, $d=\alpha a$; $\phi(z)=\alpha/z$ means $a=d=0$, $c=\alpha b$.
--
--   Differences from the source:
--   - encoding: ϕ(z) = αz or ϕ(z) = α/z as maps of the Riemann sphere → (b = 0 ∧ c = 0 ∧ d = αa) ∨ (a = 0 ∧ d = 0 ∧ c = αb); reason: two Möbius maps agree on the sphere exactly when their coefficient vectors are proportional; this avoids Lean's x/0 = 0
--   - encoding: ϕ permutes µ_m → Set.BijOn ϕ µ_m µ_m, with ϕ evaluated by complex division; reason: no pole on µ_m, so the division is the true value on µ_m
-- source:
--   Liu and Meng, A Dichotomy for Complex Boolean Holant with Binary Disequality, arXiv:2609.00219 (revised version, source.pdf sha256 b651e424…), p. F-71 (PDF p. 87), Lemma F.6.9

import Mathlib

set_option autoImplicit false

namespace DiseqHolant.Dichotomy

/-- **Lemma F.6.9 (Möbius stabilizer of a root polygon).** Let `m ≥ 3`, and let the Möbius map
`ϕ : z ↦ (c + dz)/(a + bz)`, `ad − bc ≠ 0`, have no pole on `µ_m` and permute `µ_m`. Then
`ϕ(z) = αz` or `ϕ(z) = α/z`, `α ∈ µ_m`. Liu and Meng, *A Dichotomy for Complex Boolean Holant with Binary Disequality*,
arXiv:2609.00219 (revised version, source.pdf sha256 b651e424…), p. F-71 (PDF p. 87), Lemma F.6.9.

**Formalization Note.** `µ_m = {z : z^m = 1}`. "No pole on `µ_m`" is `a + bz ≠ 0` there, so the
division is the true quotient on `µ_m`; "permute" is a bijection of `µ_m` onto itself. The
conclusion is equality of Möbius maps of the Riemann sphere, i.e. proportionality of coefficient
vectors: `ϕ(z) = αz` iff `b = c = 0`, `d = αa`; `ϕ(z) = α/z` iff `a = d = 0`, `c = αb`. -/
theorem lemma_F_6_9 (m : ℕ) (hm : 3 ≤ m) (a b c d : ℂ) (hdet : a * d - b * c ≠ 0)
    (hpole : ∀ z : ℂ, z ^ m = 1 → a + b * z ≠ 0)
    (hperm : Set.BijOn (fun z : ℂ => (c + d * z) / (a + b * z))
      {z : ℂ | z ^ m = 1} {z : ℂ | z ^ m = 1}) :
    ∃ α : ℂ, α ^ m = 1 ∧ ((b = 0 ∧ c = 0 ∧ d = α * a) ∨ (a = 0 ∧ d = 0 ∧ c = α * b)) := by sorry

end DiseqHolant.Dichotomy
