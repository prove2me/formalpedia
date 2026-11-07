-- Prove2me | Theorems.Thm_CoDecompFO_lemma_5_78
-- name    : CoDecompFO.lemma_5_78
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:49:02.986299+00:00
-- url     : https://prove2.me/theorems/808493a7-644f-4dd2-b843-d32a9a7b8f19
-- title:
--   Lemma 5.78 (corrected: non-empty strategies; $\psi$ for $\varphi$) — truth in the limit and supported hypotheticals at the root
-- statement:
--   Let $\mathcal T$ be a tree co-decomposition rooted at $r$ and $\psi$ a matrix on $[2\ell]$. Then
--   $$
--   \lim\mathcal T\models\forall x_1\exists y_1\cdots\forall x_\ell\exists y_\ell\;\psi(\vec x,\vec y)
--   $$
--   if and only if there is a supported $\ell$-hypothetical at $r$, that is $H=(\pi_r)_*(S[G[r]])$ for an $\ell$-strategy $S$ on the partial limit $G[r]$ with non-empty responses, such that the head of every hypothesis occurring in a $0$-hypothetical of $H$ satisfies $\psi$.
--
--   It moves the test from the limit to the root bag: projection does not change heads.
--
--   Differences from the source:
--   - correction: a supported ℓ-hypothetical from any strategy, under the powerset that allows empty responses → a strategy with non-empty responses at every level; reason: the printed form is false on the same one-point instance as Lemma 5.16, with a one-bag tree
--   - correction: the head of every hypothesis "satisfies φ" → the head satisfies the matrix ψ; reason: a head is a structure on [2ℓ] and φ is the quantified sentence, which is false on some heads where ψ holds; the proof of Theorem 1.16 says "the quantifier-free part of φ"
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Lemma 5.78, p.40; ¶5.77, p.40

import Mathlib
import Definitions.Def_CoDecompFO_HTh
import Definitions.Def_CoDecompFO_Lim

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- **Lemma 5.78**, with non-empty strategies and `ψ` for `φ` (Bumpus et al., arXiv:2611.04658, held
file sha256 d550d7af…, p.40): "Take an FO-formula φ = ∀x₁∃y₁,…,∀x_ℓ∃y_ℓ ψ(x⃗,y⃗) in alternating prenex
form over a signature σ and consider a tree co-decomposition T rooted at some node r. Then limT ⊨ φ if
and only if there is a supported ℓ-hypothetical H ar r such that the head of every hypothesis occurring
in a 0-hypothetical of H satisfies φ."

"Supported" is ¶5.77 (p.40): `H = (π_r)_*(S[G[r]])` for an `ℓ`-strategy `S` on `G[r]`, here with
non-empty responses (¶5.9).

**Formalization Note** Without `Strat.Total` the statement fails, on the same instance as Lemma 5.16. The
head is a structure on `[2ℓ]`, so "satisfies φ" must mean the matrix `ψ`, as the proof of Theorem 1.16
(p.41) says: "the quantifier-free part of φ". -/
theorem lemma_5_78 {σ : Sig} (T : CoDecomp σ) (r : Fin T.b) (ℓ : ℕ)
    (ψ : σ.lang.BoundedFormula Empty (2 * ℓ)) (hψ : IsMatrix ψ) :
    AltSat (G := T.Lim) ψ ℓ [] ↔
      ∃ S : Strat (T.PartialLim r r) ℓ, Strat.Total ℓ S ∧
        AllHyp ψ ℓ (push (T.partialProj r r) ℓ (ind σ (2 * ℓ) ℓ S [])) := by sorry

end CoDecompFO
