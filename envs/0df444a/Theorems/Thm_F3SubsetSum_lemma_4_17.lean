-- Prove2me | Theorems.Thm_F3SubsetSum_lemma_4_17
-- name    : F3SubsetSum.lemma_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:31:16.790849+00:00
-- url     : https://prove2.me/theorems/2420c2b5-cd6c-4514-9d98-934bdce71cec
-- title:
--   Lemma 4.17 — a $\mathcal B$-invariant monomial subspace $W_{\mathcal A}$ with $\bar\rho(W_{\mathcal A})\le\bar\rho(W)$
-- statement:
--   Let $q\ge3$ be prime, $D\ge2$, and $W\subseteq\overline R{}_D^*$ a nonzero subspace. There is a family $\mathcal A$ of reduced degree-$D$ monomials such that $W_{\mathcal A}=\langle e_\alpha : x^\alpha\in\mathcal A\rangle$ is $\mathcal B$-invariant and
--
--   $$\dim W_{\mathcal A}=\dim W,\qquad \operatorname{rank}\bigl(\overline C_{x_1}|_{W_{\mathcal A}}\bigr)=\bar\rho(W_{\mathcal A})\le\bar\rho(W),$$
--
--   where $\overline C_{x_1}$ is the contraction by the linear form $L=x_1$ (the generic contraction with the coefficients of $L$ substituted). The proof is a shifting argument through Borel's fixed-point theorem.
--
--   Differences from the source:
--   - encoding: the standing integer D ≥ 2 of §4.1 (eq. (29), p.18), left implicit in the statement → hypothesis D ≥ 2; reason: R*_{D−2} is undefined for D < 2 (natural-number subtraction would make it R*_0)
--   - encoding: x₁ for arbitrary n → hypothesis 0 < n, x₁ the variable of index 0; reason: names x₁; a nonzero W ⊆ R̄*_D with D ≥ 2 already forces n ≥ 1
--   - encoding: W_𝒜 is ℬ-invariant: gW_𝒜 = W_𝒜 for g ∈ ℬ, (gλ)(f) = λ(g⁻¹f) → λ ∘ g ∈ W_𝒜 for all λ ∈ W_𝒜 and g ∈ ℬ; reason: equivalent because ℬ is a group acting on each R̄_d (closed under inverses)
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Lemma 4.17, p.26 (proof pp.26–27)

import Mathlib
import Definitions.Def_F3SubsetSum_TruncatedRing
import Definitions.Def_F3SubsetSum_SymbolicRank
import Definitions.Def_F3SubsetSum_MonomialShadow
import Definitions.Def_F3SubsetSum_BorelAction

namespace F3SubsetSum

/-- **Lemma 4.17** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Lemma 4.17, p.26;
proof pp.26–27): "For every nonzero subspace W ⊆ R̄*_D, there is a family 𝒜 of reduced
degree-D monomials such that W_𝒜 = ⟨e_α : x^α ∈ 𝒜⟩ is ℬ-invariant and
dim(W_𝒜) = dim(W), rank(C̄_{x_1}|_{W_𝒜}) = ρ̄(W_𝒜) ≤ ρ̄(W).
Here we use C̄_L for the contraction map obtained by substituting coefficients of L into C̄_{L_z}."

Over the algebraic closure `F̄_q`, `q ≥ 3` prime, `D ≥ 2`. `ℬ` is the triangular group of p.26,
`W_𝒜` the span of the coefficient functionals `e_α`, and `C̄_{x_1}` the contraction by the linear
form `L = x_1`, whose rank on `W_𝒜` is taken over `F̄_q`.

**Formalization Note** `x_1` is the variable with index `0`; the hypothesis `0 < n` only names it
(a nonzero `W ⊆ R̄*_D` with `D ≥ 2` forces `n ≥ 1`). `ℬ`-invariance is stated in the
inverse-free form of `IsBorelInvariant`. -/
theorem lemma_4_17 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hn : 0 < n) (hD : 2 ≤ D)
    (W : Submodule (AlgebraicClosure (ZMod q))
      (Module.Dual (AlgebraicClosure (ZMod q)) (Rd (AlgebraicClosure (ZMod q)) n q D)))
    (hW : W ≠ ⊥) :
    ∃ 𝒜 : Finset (Fin n →₀ ℕ),
      (∀ α ∈ 𝒜, (∀ j, α j < q) ∧ monoDeg α = D) ∧
      IsBorelInvariant q D (monomialSpan (K := AlgebraicClosure (ZMod q)) q D 𝒜) ∧
      Module.finrank (AlgebraicClosure (ZMod q))
          (monomialSpan (K := AlgebraicClosure (ZMod q)) q D 𝒜) =
        Module.finrank (AlgebraicClosure (ZMod q)) W ∧
      Module.finrank (AlgebraicClosure (ZMod q))
          (LinearMap.range ((contraction (AlgebraicClosure (ZMod q)) n q D
            (Pi.single (⟨0, hn⟩ : Fin n) 1)).domRestrict
              (monomialSpan (K := AlgebraicClosure (ZMod q)) q D 𝒜))) =
        symbolicRank (AlgebraicClosure (ZMod q)) n q D
          (monomialSpan (K := AlgebraicClosure (ZMod q)) q D 𝒜) ∧
      symbolicRank (AlgebraicClosure (ZMod q)) n q D
          (monomialSpan (K := AlgebraicClosure (ZMod q)) q D 𝒜) ≤
        symbolicRank (AlgebraicClosure (ZMod q)) n q D W := by sorry

end F3SubsetSum
