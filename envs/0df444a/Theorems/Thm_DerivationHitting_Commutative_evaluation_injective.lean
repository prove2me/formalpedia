-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_evaluation_injective
-- name    : DerivationHitting.Commutative.evaluation_injective
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:43.912585+00:00
-- url     : https://prove2.me/theorems/f7cf64ad-9965-4b22-887c-0a3d4cec4ae3
-- title:
--   Lemma 2.3 — Injectivity of the associated evaluation
-- statement:
--   Let $F$ be a characteristic-zero field and $n\in\mathbb N$. Let $b_i\in F(t)$ and $P_i\in F[[t]]$ for $1\le i\le n$, with $P_i'=b_i$ in $F((t))$. Define $D_b=\partial_t+\sum_i b_i\partial_{x_i}$ on $R=F(t)[x_1,\ldots,x_n]$. Suppose its ring of constants is exactly the embedded base field $F$. Then the substitution map is injective:
--   $$
--    \Phi_P:R\longrightarrow F((t)),\qquad h(t,x)\longmapsto h(t,P_1(t),\ldots,P_n(t)),\qquad
--    \Phi_P(h)=\Phi_P(g)\ \Longrightarrow\ h=g.
--   $$
--   The coefficient map is the canonical embedding $F(t)\hookrightarrow F((t))$. This is the general injectivity result used for the concrete logarithmic substitution. The primitive compatibility is part of the associated-map setup on the same page, rather than a restriction added to the lemma.
--
--   Differences from the source:
--   - encoding: variables indexed by 1,…,n → variables indexed by Fin n, with integer parameter i.val+1; reason: this is a bijective reindexing and the first kernel is nonzero
--   - encoding: the associated map defined above the lemma → explicit tuple of power-series primitives with derivative equality in Laurent series; reason: these are precisely the data used in the source to define the associated map
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026), p. 10, Lemma 2.3 and its preceding associated-evaluation setup; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/577.pdf

import Definitions.Def_DerivationHitting_Commutative_DifferentialData
open scoped RatFunc

namespace DerivationHitting.Commutative
theorem evaluation_injective {F : Type*} [Field F] [CharZero F] {n : ℕ}
    (b : Fin n → RatFunc F) (P : Fin n → PowerSeries F)
    (hP : arePrimitives b P) (hD : hasTrivialConstants b) :
    Function.Injective (associatedEvaluation P) := by sorry
end DerivationHitting.Commutative
