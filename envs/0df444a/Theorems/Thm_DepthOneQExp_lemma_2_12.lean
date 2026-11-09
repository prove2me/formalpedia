-- Prove2me | Theorems.Thm_DepthOneQExp_lemma_2_12
-- name    : DepthOneQExp.lemma_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:48:10.543053+00:00
-- url     : https://prove2.me/theorems/ed362954-35cd-44c5-bc08-0fe6df9ba688
-- title:
--   Lemma 2.12: $\lambda_{\min}$ of the average over $\Sigma_{3s}$ is at least $-1+1/63$
-- statement:
--   Let $G=\mathrm{SL}(3s;\mathbb F_2)$ with $s\ge1$ and $S=\Sigma_{3s}$. For every finite-dimensional unitary representation $\rho$ of $G$,
--   $$
--   \lambda_{\min}\Big(\frac1{|S|}\sum_{g\in S}\rho(g)\Big) \ge -1+\frac1{63}.
--   $$
--
--   Together with Lemma 2.4 (which bounds the top of the spectrum) this gives a two-sided bound on the averaging operator of Kassabov's generators.
--
--   **Formalization Note** The average is Hermitian because every element of $\Sigma_{3s}$ is an involution; $\lambda_{\min}\ge c$ is stated as $\mathrm{Re}\langle v,Av\rangle\ge c\|v\|^2$ for all $v$. $|S|=14$ counts the family with multiplicity.
--
--   Differences from the source:
--   - encoding: λ_min((1/|S|) Σ ρ(g)) ≥ c → Re⟨v, A v⟩ ≥ c‖v‖² for all v; reason: A is Hermitian (involutive generators); equivalent
--   - encoding: the set Σ_{3s}, |S| = 14 → the indexed family sigma s : Fin 14 → SL(3s; F₂), average over the 14 indices; reason: the paper counts |S| = 14 in its proof; for s = 1 entries repeat
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Lemma 2.12, Eq. (2.21), p.10

import Mathlib
import Definitions.Def_ConstGapCircuits_spectralGap
import Definitions.Def_DepthOneQExp_sigma

namespace DepthOneQExp

open scoped InnerProductSpace

/-- Lemma 2.12 (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group
and applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Lemma 2.12, Eq. (2.21),
p.10): for `G = SL(3s; 𝔽₂)`, `S = Σ_{3s}` and every finite-dimensional unitary representation `ρ`,
`λ_min((1/|S|) Σ_{g ∈ S} ρ(g)) ≥ −1 + 1/63`.

**Formalization Note** The average is Hermitian (every element of `Σ_{3s}` is an involution), and
`λ_min ≥ c` is stated as the Rayleigh bound `Re⟨v, A v⟩ ≥ c ‖v‖²` for all `v`. `|S| = 14` counts the
family with multiplicity. -/
theorem lemma_2_12 (s : ℕ) (hs : 1 ≤ s)
    (ρ : ConstGapCircuits.UnitaryRep (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)))
    (v : EuclideanSpace ℂ (Fin ρ.dim)) :
    (-1 + 1 / 63 : ℝ) * ‖v‖ ^ 2 ≤
      RCLike.re ⟪v, Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((1 / 14 : ℂ) • ∑ i : Fin 14, (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)) v⟫_ℂ := by sorry

end DepthOneQExp
