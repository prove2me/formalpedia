-- Prove2me | Theorems.Thm_DSICHardRev_fact_2_24
-- name    : DSICHardRev.fact_2_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:41.432193+00:00
-- url     : https://prove2.me/theorems/9004db35-d013-45c9-8a3d-fb4fd1441d7f
-- title:
--   Fact 2.24 — superadditivity of conditional mutual information
-- statement:
--   Let $X_1,\dots,X_n,Y,Z$ be random variables with finite ranges such that $X_1,\dots,X_n$ are independent conditioned on $Z$. Then
--   $$\mathbb I(X_1,\dots,X_n;Y\mid Z)\;\ge\;\sum_{i\in[n]}\mathbb I(X_i;Y\mid Z).$$
--
--   It is used to split the information a group's messages carry about the vector $j_k$ into the coordinates $j_{k,\ell}$ (Lemma 3.8).
--
--   **Formalization Note** Conditional independence given $Z$ means that for every $z$ with $\Pr[Z=z]>0$ the conditional law of $(X_1,\dots,X_n)$ given $Z=z$ is the product of the conditional laws of the $X_i$. The $X_i$ may have different ranges.
--
--   Differences from the source:
--   - reading: discrete random variables → random variables with finite ranges on a finite probability space; reason: Definition 2.22's bound log|X| presupposes finite ranges and every variable the paper uses is finite; the quantities depend only on the joint law
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.5, p.11, Fact 2.24

import Mathlib
import Definitions.Def_DSICHardRev_Information

namespace DSICHardRev

/-- **Fact 2.24 (Superadditivity of Mutual Information)** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §2.5, p.11):
let `X_1, …, X_n, Y, Z` be discrete random variables, where `X_1, …, X_n` are independent conditioned
on `Z`. Then `𝕀(X_1, …, X_n ; Y | Z) ≥ ∑_i 𝕀(X_i ; Y | Z)`.

**Formalization Note.** The random variables have finite ranges and live on a finite probability
space `P`. Conditional independence given `Z`: for every `z` with `Pr[Z = z] > 0`, the conditional
law of `(X_1, …, X_n)` given `Z = z` is the product of the conditional laws of the `X_i`. -/
theorem fact_2_24 {Ω : Type} [Fintype Ω] {n : ℕ} {α : Fin n → Type} [∀ i, Fintype (α i)]
    {β γ : Type} [Fintype β] [Fintype γ] (P : FinProb Ω) (X : (i : Fin n) → Ω → α i)
    (Y : Ω → β) (Z : Ω → γ)
    (hind : ∀ z, 0 < P.prob (fun ω => Z ω = z) → ∀ a : (i : Fin n) → α i,
      P.condLaw (fun ω i => X i ω) Z z a = ∏ i, P.condLaw (X i) Z z (a i)) :
    ∑ i, P.mutualInfo (X i) Y Z ≤ P.mutualInfo (fun ω i => X i ω) Y Z := by sorry

end DSICHardRev
