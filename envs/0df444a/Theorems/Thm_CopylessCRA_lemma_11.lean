-- Prove2me | Theorems.Thm_CopylessCRA_lemma_11
-- name    : CopylessCRA.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:37.2573+00:00
-- url     : https://prove2.me/theorems/f09b24d5-b417-441a-87e3-2613de992fd7
-- title:
--   Lemma 11, p.9 — $\mathcal W_k$ is closed; its identity component is triangular; its unipotent elements are translations and commute
-- statement:
--   Let $\mathfrak A_k=(\overline{\mathbb Q}^\times\ltimes\overline{\mathbb Q})^k\rtimes S_k$ be the group of affine coordinate permutations of affine $k$-space over $\overline{\mathbb Q}$ and $\mathcal W_k=\{B_R:R\in\mathfrak A_k\}\subseteq GL(V_k\otimes\overline{\mathbb Q})$. Then
--
--   1. $\mathcal W_k$ is a Zariski-closed subgroup;
--   2. its identity component consists of the pullbacks of the maps $x\mapsto(\alpha_ix_i+\beta_i)_i$ ($\alpha_i\ne0$);
--   3. the identity component preserves the complete rational flag spanned by the squarefree monomials taken in order of nondecreasing degree;
--   4. the unipotent elements of $\mathcal W_k$ are exactly the pullbacks of translations $x\mapsto(x_i+\beta_i)_i$; in particular they commute pairwise.
--
--   Differences from the source:
--   - encoding: $GL(V_k\otimes\overline{\mathbb Q})$ → invertible matrices indexed by subsets of $\{1,\dots,k\}$ (the squarefree monomial basis); reason: the basis is the one the paper uses
--   - reading: "the complete rational flag spanned by the squarefree monomials taken in order of nondecreasing degree" → for every injective enumeration of the subsets that increases strictly with $|I|$, every element of the identity component is upper triangular; reason: the paper does not fix how monomials of equal degree are ordered; the statement holds for every such order
--   - encoding: Zariski closure via polynomials in the entries and $\det^{-1}$ → polynomials in the entries, closed sets taken relative to $GL_d(\overline{\mathbb Q})$; reason: multiplying by a power of $\det$, a unit on $GL$, gives the same closed subsets of $GL$
--   - encoding: identity component $\mathcal G^\circ$ of the algebraic group → the union of all Zariski-connected subsets of $\mathcal G$ containing $1$ (the connected component of $1$); reason: this is the identity component of a linear algebraic group; its group and finite-index properties (A1) are theorems, not definitions
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Lemma 11, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_CopylessCRA_IsCopylessMap
import Definitions.Def_CopylessCRA_zariskiClosure

namespace CopylessCRA

/-- **Lemma 11.** `𝒲_k` is a closed subgroup. Its identity component consists of the pullbacks of the
maps `x ↦ (α_i x_i + β_i)_i`; it preserves the complete rational flag spanned by the squarefree
monomials taken in order of nondecreasing degree. The unipotent elements of `𝒲_k` are exactly the
pullbacks of translations; in particular they commute pairwise.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Lemma 11, p.9 (PDF p.11).

**Formalization Note** `𝔄_k = (ℚ̄× ⋉ ℚ̄)^k ⋊ S_k` and `𝒲_k = {B_R : R ∈ 𝔄_k} ⊆ GL(V_k ⊗ ℚ̄)` (p.9),
with matrices in the squarefree monomial basis `(x_I)_{I ⊆ {1,…,k}}` (`affinePullbackGroup`).
"Preserves the flag" is stated for every enumeration of the subsets that is injective and
nondecreasing in `|I|`: each element of the identity component is upper triangular in it. In
`α_i x_i + β_i` the `α_i` are nonzero (they are elements of `ℚ̄×`). -/
theorem lemma_11 (k : ℕ) :
    (∃ G : Subgroup (Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar)ˣ,
      (G : Set (Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar)ˣ) = affinePullbackGroup Qbar k) ∧
    IsZariskiClosed (affinePullbackGroup Qbar k) ∧
    identityComponent (affinePullbackGroup Qbar k) =
      {g : (Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar)ˣ | ∃ a b : Fin k → Qbar, (∀ i, a i ≠ 0) ∧
        (g : Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar) =
          pullbackMatrix (fun i => MvPolynomial.C (a i) * MvPolynomial.X i + MvPolynomial.C (b i))} ∧
    (∀ ord : Finset (Fin k) → ℕ, Function.Injective ord →
      (∀ I J : Finset (Fin k), I.card < J.card → ord I < ord J) →
      ∀ g ∈ identityComponent (affinePullbackGroup Qbar k),
        (g : Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar).BlockTriangular ord) ∧
    (∀ g ∈ affinePullbackGroup Qbar k,
      IsUnipotent (g : Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar) ↔
        ∃ b : Fin k → Qbar, (g : Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar) =
          pullbackMatrix (fun i => MvPolynomial.X i + MvPolynomial.C (b i))) ∧
    ∀ g ∈ affinePullbackGroup Qbar k, ∀ h ∈ affinePullbackGroup Qbar k,
      IsUnipotent (g : Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar) →
      IsUnipotent (h : Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar) →
        Commute (g : Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar)
          (h : Matrix (Finset (Fin k)) (Finset (Fin k)) Qbar) := by sorry

end CopylessCRA
