-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_4_6
-- name    : EuclidKSteiner.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:29.198057+00:00
-- url     : https://prove2.me/theorems/e974120d-1615-452b-ad88-96cb7c355626
-- title:
--   Lemma 4.6 — union, cost shift and disjoint product preserve representative families
-- statement:
--   Fix $r$, a ground set $U_0$ and a function $\Psi$ on subsets of $U_0$.
--
--   1. **Union.** If $\widehat{\mathcal A}_j$ represents the weighted family $\mathcal A_j$ of $p$-element sets ($p\le r$) for $j=1,\dots,m$, then $\bigcup_j\widehat{\mathcal A}_j$ represents $\bigcup_j\mathcal A_j$.
--   2. **Common cost shift.** If $\widehat{\mathcal A}$ represents the $p$-family $\mathcal A$ ($p\le r$), then $\mathrm{shift}_\delta(\widehat{\mathcal A})$ represents $\mathrm{shift}_\delta(\mathcal A)$ for every $\delta\in\mathbb R$.
--   3. **Disjoint product.** If $\widehat{\mathcal A}$ represents the $p$-family $\mathcal A$, $\widehat{\mathcal A}'$ represents the $p'$-family $\mathcal A'$, and $p+p'\le r$, then $\widehat{\mathcal A}\star\widehat{\mathcal A}'$ represents $\mathcal A\star\mathcal A'$ as a family of $(p+p')$-element sets.
--
--   Applied with $\Psi=\Phi$ these closure properties justify compressing every table entry of the dynamic program.
--
--   Differences from the source:
--   - generalization: representative families for Φ → representative families for an arbitrary Ψ : Finset U → ℝ over an arbitrary finite ground set U₀; reason: the operations and the proof use nothing about Φ; Ψ = Φ, U₀ = P is an instance
--   - encoding: Definition 2.1, equality of two maxima with empty maximum −∞ → Representative: Â ⊆ 𝒜 and every disjoint pair of 𝒜 is matched by a disjoint pair of Â with at least the same score; reason: equivalent given Â ⊆ 𝒜
--   - encoding: families 𝒜_1, …, 𝒜_m → families indexed by Fin m; reason: 0-based indexing
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.6, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_EuclidKSteiner_Representative

namespace EuclidKSteiner

/-- **Lemma 4.6.** Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean
k-Steiner Tree*, STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.6, p.18 (PDF p.20):
"Fix r. Each of the following operations preserves representative families for Φ and r
attachments: replacing every input family by a representative subfamily produces a representative
subfamily of the output. 1. Union. … 2. Common cost shift. … 3. Disjoint product. …"

For every function `Ψ` on finite subsets of a ground set `U₀` and every `r`:
1. (Union.) If `Â_j` represents the weighted `p`-family `𝒜_j` (`p ≤ r`) for `j = 1, …, m`, then
   `⋃_j Â_j` represents `⋃_j 𝒜_j`.
2. (Common cost shift.) If `Â` represents the `p`-family `𝒜` (`p ≤ r`), then `shift_δ(Â)` represents
   `shift_δ(𝒜)` for every `δ ∈ ℝ`.
3. (Disjoint product.) If `Â` represents the `p`-family `𝒜`, `Â'` represents the `p'`-family `𝒜'`, and
   `p + p' ≤ r`, then `Â ⋆ Â'` represents `𝒜 ⋆ 𝒜'` as a `(p + p')`-family.

**Formalization Note** Stated for an arbitrary `Ψ` (the page states it for `Ψ = Φ`); the operations
and the proof use nothing about `Φ`. -/
theorem lemma_4_6 {U : Type*} [DecidableEq U] (Ψ : Finset U → ℝ) (U₀ : Finset U) (r : ℕ) :
    (∀ (m p : ℕ) (𝒜 Â : Fin m → Set (Finset U × ℝ)), p ≤ r →
      (∀ j, IsWeightedFamily U₀ p (𝒜 j)) → (∀ j, Representative Ψ U₀ r p (𝒜 j) (Â j)) →
      Representative Ψ U₀ r p (famUnion 𝒜) (famUnion Â)) ∧
    (∀ (p : ℕ) (δ : ℝ) (𝒜 Â : Set (Finset U × ℝ)), p ≤ r → IsWeightedFamily U₀ p 𝒜 →
      Representative Ψ U₀ r p 𝒜 Â → Representative Ψ U₀ r p (famShift δ 𝒜) (famShift δ Â)) ∧
    (∀ (p p' : ℕ) (𝒜 Â 𝒜' Â' : Set (Finset U × ℝ)), p + p' ≤ r →
      IsWeightedFamily U₀ p 𝒜 → IsWeightedFamily U₀ p' 𝒜' →
      Representative Ψ U₀ r p 𝒜 Â → Representative Ψ U₀ r p' 𝒜' Â' →
      Representative Ψ U₀ r (p + p') (famProd 𝒜 𝒜') (famProd Â Â')) := by sorry

end EuclidKSteiner
