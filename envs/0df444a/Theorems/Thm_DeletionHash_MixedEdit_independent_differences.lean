-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_independent_differences
-- name    : DeletionHash.MixedEdit.independent_differences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:13.952555+00:00
-- url     : https://prove2.me/theorems/61acab59-4ff1-47ef-9efc-189571423dc9
-- title:
--   Lemma 3.2 — independent differences
-- statement:
--   Let $w_1,\ldots,w_R$ be integer vectors indexed by the length-$L$ grams of a finite alphabet, with linearly independent reductions over $\mathbb F_2$. Fix $r\ge1$, put $Q=2^r$, and choose one shared product-uniform hash $H$. The images are independent and uniform, expressed by their full joint law:
--   $$\Pr[H(w_i)=a_i\text{ for every }i]=Q^{-R}\quad\text{for every }(a_i)\in(\mathbb F_2^r)^R.$$
--   If the vectors are catalogue rules, then $\Pr[w_1,\ldots,w_R\in K]=Q^{-R}$. Also every integer vector $v$ with $\overline v\ne0$ obeys $\Pr[H(v)=0]=Q^{-1}$. This states the joint uniformity and both exact survival formulas, all under the actual finite product law.
--
--   Differences from the source:
--   - generalization: alphabet size q≥2 and the fixed proof regime → any finite alphabet, any natural gram length and catalogue parameters, including an empty independent family; reason: the finite-product linear-map identity holds for every finite coordinate space; specializing the parameters recovers every source instance
--   - encoding: independent uniform image vectors → full joint point probabilities Q^{-R}, rule survival probability, and the one-vector zero probability; reason: joint uniformity on the finite product is equivalent to independence together with uniform marginals
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 3.2, printed p. 9 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Labels

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 3.2: full joint uniform law, rule survival, and the single-vector law. -/
theorem independent_differences {α : Type u} [Fintype α] [DecidableEq α]
    (L r R k t b : ℕ) (hr : 1 ≤ r) (w : Fin R → Spectrum α L)
    (hw : LinearIndependent (ZMod 2) (fun i => parity (w i))) :
    (∀ a : Fin R → Label r,
      uniformProbability (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
        1 / ((2 : ℝ)^r)^R) ∧
    ((∀ i, w i ∈ Catalogue k L t b) →
      uniformProbability (fun ξ : HashSample α L r => ∀ i, Survives k t b ξ (w i)) =
        1 / ((2 : ℝ)^r)^R) ∧
    (∀ v : Spectrum α L, parity v ≠ 0 →
      uniformProbability (fun ξ : HashSample α L r => hash ξ v = 0) = 1 / (2 : ℝ)^r) := by sorry

end DeletionHash.MixedEdit
