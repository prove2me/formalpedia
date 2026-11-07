-- Prove2me | Theorems.Thm_BorderD4_lemma_4_8
-- name    : BorderD4.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:59:32.889203+00:00
-- url     : https://prove2.me/theorems/c7b5679d-8ff0-4235-92c5-79204fa402ba
-- title:
--   Lemma 4.8: specialization at $\varepsilon=0$
-- statement:
--   Let $R=F[[\varepsilon]]$ and $K=F((\varepsilon))$, with $F$ algebraically closed, and let $\pi:R[x]\to F[x]$ send $\varepsilon$ to $0$. For a prime ideal $p\subseteq K[x]$ let $I=p\cap R[x]$, $J=\pi(I)$ and $X=V(J)$. Suppose $I\subseteq\langle\varepsilon,x_1,\dots,x_N\rangle$, which holds in particular if $p\subseteq\langle x_1,\dots,x_N\rangle K[x]$. Then:
--
--   1. $0\in X$;
--   2. $X$ is equidimensional of dimension $m=\dim K[x]/p$;
--   3. every irreducible component $V$ of $X$ satisfies $\deg V\le\mathrm{DEG}\,p$.
--
--   The lemma transfers the degree bound from the generic fiber of a family over $R$ to its special fiber at $\varepsilon=0$.
--
--   Differences from the source:
--   - encoding: the variables $x_1,\dots,x_N$ → an arbitrary finite nonempty index type; reason: any such type is $[N]$ up to renaming
--   - encoding: $\mathrm{DEG}$ as a number → the predicate `HasDEG I D`, with the conclusion $\exists D$; reason: no junk value can satisfy a bound; the Hilbert polynomial is asserted to exist
--   - encoding: irreducible varieties over algebraically closed $F$ → their prime ideals (minimal primes for components); reason: the Nullstellensatz correspondence stated on p.30
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 4.8, p.40

import Mathlib
import Definitions.Def_BorderD4_HasDEG
import Definitions.Def_BorderD4_toK
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Lemma 4.8, specialization at `ε = 0`: for a prime `p ⊆ K[x]`, `K = F((ε))`, put `I := p ∩ R[x]`, `R = F[[ε]]`, and
`J := π(I)`. If `I ⊆ ⟨ε, x⟩`, which holds in particular if `p ⊆ ⟨x⟩K[x]`, then `0 ∈ V(J)`, `V(J)` is equidimensional
of dimension `dim K[x]/p`, and every irreducible component `V` of `V(J)` has `deg V ≤ DEG p`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 4.8, p.40.

**Formalization Note** `F` is algebraically closed, §4's standing assumption (p.38), so by the Nullstellensatz the
irreducible components of `V(J)` are the `V(𝔮)` for the minimal primes `𝔮` of `J` (p.30), with `deg V(𝔮) = DEG 𝔮`
(p.31). Equidimensionality is stated for these `𝔮`. -/
theorem lemma_4_8 {F σ : Type*} [Field F] [IsAlgClosed F] [Fintype σ] [Nonempty σ]
    (p : Ideal (MvPolynomial σ (LaurentSeries F))) [p.IsPrime] :
    (p ≤ Ideal.span (Set.range X) → p.comap toK ≤ epsXIdeal F σ) ∧
    (p.comap toK ≤ epsXIdeal F σ →
      (∀ g ∈ (p.comap toK).map (specialize (F := F) (σ := σ)), eval (0 : σ → F) g = 0) ∧
      ∀ 𝔮 ∈ ((p.comap toK).map (specialize (F := F) (σ := σ))).minimalPrimes,
        ringKrullDim (MvPolynomial σ F ⧸ 𝔮) = ringKrullDim (MvPolynomial σ (LaurentSeries F) ⧸ p) ∧
        ∃ D₁ D₂, HasDEG 𝔮 D₁ ∧ HasDEG p D₂ ∧ D₁ ≤ D₂) := by sorry

end BorderD4
